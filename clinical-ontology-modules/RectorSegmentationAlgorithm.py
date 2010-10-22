# -*- coding: utf-8 -*-
"""
Uses RDFLib and FuXi's InfixOWL syntax to decompose a massive
OWL ontology (GALEN) into logically consistent subsections via
a segementation algorithm outlined by Alan Rector and Julian 
Seidenberg.
"""
import os,re,sys,sha, time, pprint
import httplib, urllib
from cStringIO import StringIO
from urllib import quote
from rdflib.term_utils import *
from rdflib.util import first
from rdflib import URIRef, store, plugin, BNode, RDF, RDFS, Namespace, Literal
from rdflib.store import Store, NO_STORE, VALID_STORE, CORRUPTED_STORE
from rdflib.Graph import Graph, ConjunctiveGraph
from rdflib.sparql.QueryResult import SPARQL_XML_NAMESPACE
from FuXi.Syntax.InfixOWL import *

DEPTH_LIMIT=1

INCLUDE_ROLE_HIERARCHY_DESCENDENCY = False

SKOS       = Namespace('http://www.w3.org/2008/05/skos#')
GALEN      = Namespace('http://www.co-ode.org/ontologies/galen#')
GALEN_GRAPH=URIRef('http://www.co-ode.org/ontologies/galen')
FMA        = Namespace('http://purl.org/obo/owl/FMA#')
FMA_GRAPH  = URIRef('tag@metacognition.info:FMA')
OPENCYC    = Namespace('http://www.cyc.com/2004/06/04/cyc#')

PARTITIVE_ATTRS    = GALEN.PartitiveAttribute
FUNCTIONAL_ATTRS   = GALEN.FunctionalAttribute
MOD_ATTRS          = GALEN.ModifierAttribute
LOCATIVE_ATTRS     = GALEN.LocativeAttribute
STRUCTURAL_ATTRS   = GALEN.StructuralAttribute
CONSTRUCTIVE_ATTRS = GALEN.ConstructiveAttribute

#It was found that the combination of Partitive, Functional and Modifier
#properties produced the largest ontology that could still be classified
#successfully.
attributeExlusion=[]#STRUCTURAL_ATTRS,
                   #PARTITIVE_ATTRS,
                   #FUNCTIONAL_ATTRS,                    
                   #GALEN.InverseStructuralAttribute]
                   #LOCATIVE_ATTRS,
                   #GALEN.InverseLocativeAttribute]

def transitiveGenerator(graph,
                        node,
                        path=RDFS.subClassOf,
                        upDirection=False,
                        cycleDetection=None):
    cycleDetection=cycleDetection and cycleDetection or set()
    if not upDirection:
        rt = graph.subjects(object=node,predicate=path)
    else:
        rt = graph.objects(subject=node,predicate=path)
    for o in rt:
        if o in cycleDetection:
            return
        yield o 
        cycleDetection.add(o)
        for o2 in transitiveGenerator(graph,
                                      o,
                                      path=path,
                                      upDirection=upDirection,
                                      cycleDetection=cycleDetection.copy()):
            yield o2

def ExtractList(lst,graph,targetGraph,DEBUG=False):
    #print lst,type(lst)
    for s,p,o in graph.triples((lst,None,None)):
        #print "\t",s,p,o
        targetGraph.add((s,p,o))
    for nextLink in graph.objects(subject=lst,predicate=RDF.rest):
        ExtractList(nextLink,graph,targetGraph)    

def EraseList(lst,targetGraph):
    nxt=list(targetGraph.objects(subject=lst,predicate=RDF.rest))
    for s,p,o in targetGraph.triples((lst,None,None)):
        assert p in [RDF.first,RDF.rest]
        targetGraph.remove((s,p,o))
    for n in nxt:
        EraseList(n,targetGraph)    

extractOboDefSPARQL="SELECT ?def WHERE { ?defObj rdfs:label ?def }"

extractOboSynonym="SELECT ?syn WHERE { ?synObj rdfs:label ?syn }"

OBO_OWL=Namespace('http://www.geneontology.org/formats/oboInOwl#')

def fmaExtractFunc((s,p,o),targetGraph,srcGraph):
    if p.startswith(OBO_OWL):
        if p == OBO_OWL.hasDefinition:
            for d in srcGraph.query(extractOboDefSPARQL,
                                    initBindings={Variable('defObj'):o},
                                    initNs={'oboInOwl':OBO_OWL,
                                            'rdfs':RDFS.RDFSNS}):
                targetGraph.add((s,RDFS.comment,d))
        elif p == OBO_OWL.hasExactSynonym:
            for d in srcGraph.query(extractOboSynonym,
                                    initBindings={Variable('synObj'):o},
                                    initNs={'oboInOwl':OBO_OWL,
                                            'rdfs':RDFS.RDFSNS}):
                assert isinstance(d,Literal)
                targetGraph.add((s,SKOS.altLabel,d))
    else:
        defaultExtractFilterFunc((s,p,o),targetGraph,srcGraph)

def defaultExtractFilterFunc((s,p,o),targetGraph,srcGraph):
    targetGraph.add((s,p,o))
    for s,p,o in srcGraph.triples((o,RDF.type,None)):
        targetGraph.add((s,p,o))
    
def ExtractTerm(graph,
                term,
                targetGraph,
                exclRestrictions,
                filterFunc=fmaExtractFunc,
                selected = False,
                boundaryClass = None,
                minimalExtract = False):
    #".. upon removing such restrictions from defined class,
    #it frequently occurs that a definition becomes indistinguishable and
    #therefore equivalent to another similar definition. The resultant long
    #chains of equivalent classes, while not wrong, are difficult to view
    #in ontology editors (such as Prot´eg´e OWL [14]). Trivially equivalent
    #definitions are therefore transformed into primitive classes by
    #the segmentation algorithm."
    boundClass=minimalExtract
    for s,p,o in graph.triples((term,None,None)):
        if p in [OWL_NS.equivalentClass,
                 RDFS.subClassOf,
                 OWL_NS.allValuesFrom,
                 OWL_NS.someValuesFrom] and not minimalExtract:
            if selected or o not in exclRestrictions:
                #filtered restriction
                targetGraph.add((s,p,o))
            elif o in boundaryLinks:
                boundClass=True
            #add inclusion axioms even on boundary classes
            if p == RDFS.subClassOf and isinstance(s,URIRef):
                targetGraph.add((s,p,o))
        elif p in [OWL_NS.intersectionOf,OWL_NS.unionOf] and\
                not minimalExtract:
            discard=set()                
            origBoolC = BooleanClass(term,operator=p,graph=graph)
            targetGraph.add((s,p,o))
            ExtractList(o,graph,targetGraph)
            boolC = BooleanClass(term,operator=p,graph=targetGraph)                    
            for member in boolC:
                if member in exclRestrictions:
                    discard.add(member)
            if discard:
                if len(boolC) - len(discard) < 2:
                    if len(discard)==len(boolC):
                        #clear list
                        raise
                        boolC._rdfList.clear()
                    else:
                        for i in boolC:
                            if i not in discard:
                                targetGraph.add((s,RDFS.subClassOf,i))
                        EraseList(boolC._rdfList.uri,targetGraph)
                        assert (o,RDF.first,None) not in targetGraph
                        targetGraph.remove((s,p,o))                    
                        for i in discard:
                            assert (None,None,i) not in targetGraph                
                else:
                    #print s,p,repr(boolC),discard
                    oldLen=len(boolC) 
                    for i in discard:
                        del boolC[boolC.index(i)]
#                    assert len(boolC)==oldLen-1,' '.join([repr(CastClass(i,graph)) 
#                                            for i in discard])+'\n'+repr(origBoolC)+'\n'+repr(boolC)
        elif not minimalExtract or minimalExtract and p not in [
             OWL_NS.intersectionOf,
             OWL_NS.unionOf,
             OWL_NS.equivalentClass,
             RDFS.subClassOf,
             OWL_NS.allValuesFrom,
             OWL_NS.someValuesFrom]:
            filterFunc((s,p,o),targetGraph,graph)
    if boundClass: 
        c=Class(term,
                graph=targetGraph,
                comment=[Literal(".. A boundary class ..")])
        boundaryClass += c
                        
UNTYPED_QUERY="""
SELECT ?s ?p ?untyped 
{ ?s ?p ?untyped 
  OPTIONAL 
{ ?untyped rdf:type ?klass } 
FILTER(!bound(?klass) && ?p != rdfs:comment 
                      && ?p != rdfs:label 
                      && ?p != rdf:rest 
                      && ?p != owl:intersectionOf ) }"""

DANGLING_LIST=\
"""
SELECT ?lst ?obj
{ ?lst rdf:first ?obj OPTIONAL { ?s ?p ?lst } 
FILTER(!bound(?s)) }"""

def SegmentOntology(graphName,
                    classNames=[],
                    identifier=None,
                    db='referenceOntologies',
                    password='',
                    user='root',
                    FMACleanup=True):
    """
    "The basic segmentation algorithm starts with one or more classes of the 
    user’s choice and creates an extract based around those and related 
    concepts. These related classes are identified by following the ontology
     link structure."
    """
    store = plugin.get('MySQL',Store)(identifier)
    rt=store.open('user=%s,password=,host=localhost,db=%s'%(user,db),create=False)
    srcGraph = Graph(store,URIRef(graphName))
    assert len(srcGraph)
    global exclProp,exclRestrictions,boundaryLinks,touchedTerm,marker
    marker=None
    touchedTerm=set()
    exclProp = set(attributeExlusion)
    exclRestrictions=set()
    boundaryLinks=set()
    targetGraph=Graph()
    namespace_manager = NamespaceManager(Graph())
    namespace_manager.bind('galen', GALEN, override=False)
    namespace_manager.bind('owl', OWL_NS, override=False)
    namespace_manager.bind('fma',FMA,override=False)
    targetGraph.namespace_manager = namespace_manager
    termsToExtract=set()
    MAP=Namespace('http://code.google.com/p/python-dlp/wiki/ClinicalOntologyModules#')
    boundaryClass = Class(MAP.BoundaryClass,graph=targetGraph)
    boundaryClass.label = [Literal('All the boundary classes')]
    minimalExtract = set()
    for className in classNames:
#        print "Processing target class ", className
        for term,msg in extractTerm(srcGraph,
                                          className,
                                          depthLimit=DEPTH_LIMIT,
                                          target=True,
                                          originalTerms=classNames):
            if term not in exclRestrictions and term not in exclProp:
                termsToExtract.add(term)
            if isinstance(msg,TailRecursionMessage) and \
               msg.msg == INClUDED_BOUNDARY_CLASS and term not in classNames:
                minimalExtract.add(term)
    #assert GALEN.isAlphaConnectionOf not in exclProp
    for term in termsToExtract:
        if term in exclRestrictions or term in exclProp:
            continue
        print >>sys.stderr,"### Extracting: %s ###"%term
#        print "### Extracting: %s ###"%term        
#        if isinstance(term,BNode):
#            print CastClass(term,srcGraph)
        ExtractTerm(srcGraph,
                    term,
                    targetGraph,
                    exclRestrictions,
                    selected = term in classNames,
                    boundaryClass = boundaryClass,
                    minimalExtract = term in minimalExtract)
#        print CastClass(term,graph=targetGraph)
        print >>sys.stderr,len(targetGraph)
        print >>sys.stderr,"######################"
#        print "######################"
    for lst,obj in targetGraph.query(DANGLING_LIST,
                                initNs={"rdf":RDF.RDFNS,"rdfs":RDFS.RDFSNS}):
        if lst and obj:
            print "dangling list: %s rdf:first %s !"%(lst,obj)
            raise                    
    for s,p,untyped in targetGraph.query(UNTYPED_QUERY,initNs={"rdf" :RDF.RDFNS,
                                                               "rdfs":RDFS.RDFSNS,
                                                               "owl" :OWL_NS}):
        if untyped and untyped.find(OWL_NS) == -1:
            if not first(targetGraph.objects(predicate=RDF.type)):
                print (s,p,untyped)
                print CastClass(s,targetGraph)
                raise Exception(untyped)
            
    #checking trivially equivalent definitions:
    #4.1.1 Removing trivially equivalent definitions
    trivialReduction=[]
    for s,p,o in targetGraph.triples((None,OWL_NS.equivalentClass,None)):
        if False:#first(targetGraph.triples_choices((o,[OWL_NS.intersectionOf,OWL_NS.unionOf],None))):
            #bypass indirection of class equivalency axiom with boolean combination
            for _s,_p,_o in targetGraph.triples_choices((o,[OWL_NS.intersectionOf,
                                                            OWL_NS.unionOf],None)):
                targetGraph.add((s,_p,_o))
                targetGraph.remove((s,OWL_NS.equivalentClass,o)) 
                targetGraph.remove((o,None,None))
        else:
            trivialReduction.append((s,o))
    for s,o in trivialReduction:
        print >>sys.stderr,"### Reducing Trivial Equivalent Def ###"
        print >>sys.stderr,CastClass(s,targetGraph)
#        print >>sys.stderr,CastClass(o,targetGraph)
        targetGraph.remove((s,OWL_NS.equivalentClass,o))
        targetGraph.add((s,RDFS.subClassOf,o))
        print >>sys.stderr,CastClass(s,targetGraph)
        print >>sys.stderr,"######################"
    store.rollback()
    store.close()
    if FMACleanup:
        for s,p,o in targetGraph.triples((None,RDFS.subClassOf,None)):
            if (o,None,None) not in targetGraph:
                targetGraph.remove((s,p,o))
    return targetGraph

def extractAssertions(term,graph,exlusions=None):
    exclusions = exclusions and exclusions or []
    for s,p,o in graph.triples((term,None,None)):
        if not (s,p,o) in exclusions:
            yield (s,p,o) 

UNREACHABLE_LINK        = 0
REMOVED_LINK            = 1
REMOVED_LINK_FILTER     = 2
MODIFIED_CLASS          = 3        
INClUDED_BOUNDARY_CLASS = 4
class TailRecursionMessage(object):
    def __init__(self,msg,obj=None):
        self.msg = msg       
        self.obj = obj 
    def decodeMessage(self):
        if self.msg == UNREACHABLE_LINK:
            return "Unreachable link (boundary class)"
        elif self.msg == REMOVED_LINK_FILTER:
            return "Property filtered, containing restriction removed"
        elif self.msg == REMOVED_LINK:
            return "Restriction removed"
        elif self.msg == MODIFIED_CLASS:
            return "The class has been modified by the segmentation algorithm"
        else:
            raise
    def __repr__(self):
        print "Message: ", self.msg, self.obj
        
def extractTerm(graph,
                term,
                depthLimit=DEPTH_LIMIT,
                property=False,
                universe=set(),
                skipVertical=False,
                target=False,
                originalTerms=[],
                describesSelectedTerm = False):
    """
    3.4 Upwards & Downwards and Upwards from links
    
    Having selected the classes up & down the hierarchy from the target class, their
    restrictions, intersection, union and equivalent classes now need to be 
    considered: intersection and union classes can be broken apart into other types 
    of classes and processed accordingly.  Equivalent classes (defined classes which
    have another class or restriction as both their subclass and their superclass) 
    can be included like any other superclass or restriction, respectively. 
    Additionally, the superproperties and superclasses of these newly included 
    properties and classes also need to be recursively included.
    """
    #print "extractTerm(%s,%s,%s,%s,%s)"%(term,depthLimit,property,skipVertical,target)
    taxonomySkeleton=property and RDFS.subPropertyOf or RDFS.subClassOf
    superProps=None
    if term in universe:
        #We have processed this term before
        return
    
    #By default each extracted term is returned with
    #an iterator over it's statements
    termMsg = extractAssertions(term,graph)                
    if property:
        if term in touchedTerm:
            return
        else:
            touchedTerm.add(term)        
        candidates=[term]
        #transitive closure up property/role heirarchy
        for link in transitiveGenerator(graph,
                                        term,
                                        upDirection=True,
                                        path=taxonomySkeleton):
            if link in exclProp:
                #4.1 Property filtering
                #If the aim is to produce a segment for use by a human, or specialized
                #application, then filtering on certain properties is a useful approach.
                #Here we mark all accumulated, descendant properties                
                exclProp.update(candidates)
                yield term,TailRecursionMessage(REMOVED_LINK_FILTER,link)
                return 
            else:
                candidates.append(link)
        for p in candidates:
            #extract transitive closure of role subsumption (upwards)
            #if not excluded
            yield p,extractAssertions(p,graph)
        #if we want to, include descendency of extracted role hierarchy
        if INCLUDE_ROLE_HIERARCHY_DESCENDENCY:
            for link in transitiveGenerator(graph,
                                            term,
                                            upDirection=False,
                                            path=taxonomySkeleton):
                yield link,None
    else:
        if depthLimit == 0:
            #boundary class (unreachable), prune containing restriction
            yield term,TailRecursionMessage(UNREACHABLE_LINK)
            return
        else:      
            #Only skip touched terms if they are not restrictions associated
            #with selected terms
            if not describesSelectedTerm and term in touchedTerm:
                return
            else:
                touchedTerm.add(term)            
            universe.add(term)   
            #Extract transitive closure of subsumption (upwards) and 
            #equivalence (upwards)
            for skelTerm in [OWL_NS.equivalentClass,taxonomySkeleton]:
                for i in transitiveGenerator(graph,
                                             term,
                                             upDirection=True,
                                             path=skelTerm):
                    describesSelectedTerm = term in originalTerms and \
                                i in graph.objects(term,taxonomySkeleton)
                    #FIXME, need to add support for defined type handling
                    for _i,generator in extractTerm(graph,
                                                    i,
                                                    depthLimit,
                                                    property,
                                                    universe.copy(),
                                                    skipVertical=True,
                                                    originalTerms=originalTerms,
                                                    describesSelectedTerm = describesSelectedTerm):
                        yield _i,generator
            #Extract transitive closure of subsumption (downwards)
            #"The algorithm also goes down the class hierarchy from the Heart,
            #including its subclasses (in this case: UniventricularHeart). This is
            #especially relevant when segmenting an ontology that has already
            #been classified where newly inferred subclasses of a particular class
            #are likely to be of interest."
#            if target and not skipVertical and not property:
#                for i in transitiveGenerator(graph,
#                                             term,
#                                             path=taxonomySkeleton,
#                                             upDirection=False):
#                    yield i,termMsg
                                    
            #Decompose boolean classes
            #SELECT ?s ?o {{?s owl:intersectionOF ?o} 
            #                      UNION 
            #              {?s owl:unionOf        ?o}}
            for s,p,o in graph.triples_choices((term,
                                                [OWL_NS.intersectionOf,
                                                 OWL_NS.unionOf],
                                                None)):
                #use FuXi.Syntax.InfixOWL.BooleanClass to iterate over
                #boolean set operator arguments, recursively
                for member in BooleanClass(term,operator=p,graph=graph): 
                    for _i,generator in extractTerm(graph,
                                                    member,
                                                    depthLimit-1,
                                                    False,
                                                    universe.copy(),
                                                    originalTerms=originalTerms):
                        yield _i,generator        
            
            #Extract restriction components recursively
            if isinstance(term,BNode):
                #SELECT ?s ?o {{?s owl:allValuesFrom  ?o} 
                #                      UNION 
                #              {?s owl:someValuesFrom ?o}}        
                for s,p,o in graph.triples_choices((term,
                                                   [OWL_NS.allValuesFrom,
                                                    OWL_NS.someValuesFrom],
                                                    None)):
                    #"Restrictions generally have both a type (property) and a filler (class), both
                    #of which need to be included in the segment." 3.4 Upwards & Downwards ..
                    prop = first(graph.objects(subject=term,predicate=OWL_NS.onProperty))
                    #property                    
                    for _i,generator in extractTerm(graph,
                                                    prop,
                                                    depthLimit-1,
                                                    True,
                                                    universe.copy(),
                                                    originalTerms=originalTerms):
                        if isinstance(generator,TailRecursionMessage) and \
                               generator.msg == REMOVED_LINK_FILTER:
                            #"Properties are filtered by removing all restriction in which they occur."
                            # - 4.1.1 Removing trivially equivalent definitions
                            exclRestrictions.add(term)
                        else:                    
                            yield _i,generator
                    #Note, we don't increment the depth counter if the current term is
                    #a restriction that links a selected class to o
                    for _i,generator in extractTerm(graph,
                                                    o,
                                                    depthLimit-1,#describesSelectedTerm and depthLimit or depthLimit-1,
                                                    False,
                                                    universe.copy(),
                                                    originalTerms=originalTerms):
                        if isinstance(generator,TailRecursionMessage) and \
                           generator.msg == UNREACHABLE_LINK:
                            #4.2 Depth limiting using boundary classes
                            #However, if, upon reaching a certain recursion depth,
                            #calculated from the extract’s target concept, all 
                            #the links on a class are removed, this class 
                            #becomes a boundary class.
                            #Note if the current term is a restriction linking a 
                            #selected class or if this is an originally selected term
                            #we do not exclude its restrictions or mark it as a boundary class
                            #and we returned the linked/filler class even if it is unreachable
                            if describesSelectedTerm:
                                yield o,TailRecursionMessage(INClUDED_BOUNDARY_CLASS)
                            elif term not in originalTerms:
                                exclRestrictions.add(term)
                                boundaryLinks.add(term)
                        else:
                            yield _i,generator
    yield term,termMsg

def gc(path,graphName,format='xml'):
    store = plugin.get('MySQL',Store)()
    rt=store.open('user=root,password=1618,host=localhost,db=bigOnt',create=False)
    if rt == VALID_STORE:
        now = time.time()
        store.gc()
        print "Time to perform garbage collection ", time.time() - now
        print store
        store.commit()
    store.close()

def loadBigOntology(path,graphName,format='xml'):
    store = plugin.get('MySQL',Store)()
    rt=store.open('user=root,password=1618,host=localhost,db=bigOnt',create=False)
    if rt == VALID_STORE:
        pass
    elif rt == NO_STORE:
        store.open('user=root,password=1618,host=localhost,db=bigOnt',create=True)
    elif rt == CORRUPTED_STORE:
        store.destroy('user=root,password=1618,host=localhost,db=bigOnt')    
        store.open('user=root,password=1618,host=localhost,db=bigOnt',create=True)
    g=Graph(store,identifier=URIRef(graphName))
    now = time.time()
    g.parse(path,format=format)
    print "Time to parse graph ", time.time() - now
    print store
    store.commit()
    store.close()

def exportBigOnt(path,identifier,graphName,format='xml'):
    from rdflib.store.MySQLMassLoader import MySQLLoader
    store=MySQLLoader(identifier)
    g=Graph(store,identifier=URIRef(graphName))
    now = time.time()
    g.parse(path,format=format)
    print "Time to parse graph ", time.time() - now
    store.dumpRDF()    

def galenGraphs():
    store = plugin.get('MySQL',Store)()
    rt=store.open('user=root,password=1618,host=localhost,db=bigOnt',create=False)
    for g in ConjunctiveGraph(store).contexts():
        print g
    store.close()
    
def main():    
    queryGalen()

def compositeDifferentia(graph,classURIs):
    rt=[]
    lsts=[]
    for link,p,o in graph.triples_choices((None,RDF.first,classURIs)):
        end=False
        while not end:
            nxtLink=first(graph.subjects(RDF.rest,link))
            if not nxtLink:
                end=True
                lsts.append(link)
            else:
                link=nxtLink
    targets=[cl for cl,p,o in graph.triples_choices((None,OWL_NS.intersectionOf,lsts))]
    for linkTerm in [OWL_NS.equivalentClass,RDFS.subClassOf]:
        for s,p,o in graph.triples_choices((None,linkTerm,targets)):
            rt.append(s)
    return rt
    
def diseaseOntology(graphName):
    store = plugin.get('MySQL',Store)()
    rt=store.open('user=root,password=1618,host=localhost,db=bigOnt',create=False)
    srcGraph = Graph(store,URIRef(graphName))
    pathologicalPh=compositeDifferentia(srcGraph,[GALEN.PathologicalPhenomenon])
    pathologicalPh.extend(compositeDifferentia(srcGraph,[child for child in pathologicalPh]))
    pathologicalPh.append(GALEN.PathologicalPhenomenon)
    store.rollback()
    store.close()
    SegmentOntology(GALEN_GRAPH,set(pathologicalPh))
        
def extractFMAUris(path):
    g=Graph().parse(path)
    return set([uri for uri in g.subjects(RDF.type,OWL_NS.Class)
                   if uri.find(FMA)+1])      
    
def alignFMA(graph,align):
    CPR=ClassNamespaceFactory(URIRef("http://purl.org/cpr/0.85#"))
    _FMA=ClassNamespaceFactory(FMA)
    Individual.factoryGraph=graph
#    _FMA['FMA_5897'].subClassOf = [CPR['anatomical-space']]
    for spaces in graph.subjects(RDFS.subClassOf,FMA['FMA_5897']):
        g.remove((spaces,RDFS.subClassOf,None))
        Class(spaces).subClassOf = [CPR['anatomical-space']]
    
    for structures in graph.subjects(RDFS.subClassOf,FMA['FMA_67135']):
        g.remove((structures,RDFS.subClassOf,None))
        Class(structures).subClassOf = [CPR['anatomical-structure']]
    
    g.remove((FMA['FMA_55652'],RDFS.subClassOf,None))
    g.remove((FMA['FMA_9669'],RDFS.subClassOf,None))
    _FMA['FMA_55652'].subClassOf = [CPR['extra-organismal-continuant']]
    _FMA['FMA_9669'].subClassOf = [CPR['material-anatomical-entity']]
    
    removeClasses=[FMA['FMA_5897'],
                   FMA['FMA_67112'],
                   FMA['FMA_61775'],
                   FMA['FMA_62955'],
                   FMA['FMA_67165'],
                   FMA['FMA_67135'],
                   FMA['FMA_67175'],
                   FMA['FMA_85800'],
                   FMA['FMA_62955']]
    for cl in removeClasses:
        g.remove((cl,None,None))
    ont=Ontology(imports=[URIRef(align)])
            
if __name__ == '__main__':
    from optparse import OptionParser
#    exportBigOnt('fma_lite.owl',
#                 'fma_lite',
#                 FMA_GRAPH,
#                 format='xml')
#    exportBigOnt('cyc.owl',
#                 'opencyc',
#                 OPENCYC,
#                 format='xml')
    #queryGalen()
    
    parser = OptionParser()
    (options, args) = parser.parse_args()    
    
#    anatomySrc = [URIRef(args[0])]
    
    uriSrc = args[0]
    anatomySrc = uriSrc.find(FMA)+1 and [URIRef(uriSrc)] or extractFMAUris(args[0])
#    if len(sys.argv)>3:
#        align=sys.argv[3]
        
#    loadBigOntology(uri,graphName)
#    gc(uri,graphName)
#    diseaseOntology(GALEN_GRAPH)
    g=SegmentOntology(FMA,
                    db='fma',
                    classNames=anatomySrc,
                    identifier='fma')
    
    
#    alignFMA(g,align)
    print g.serialize(format='pretty-xml')
    #galenGraphs()