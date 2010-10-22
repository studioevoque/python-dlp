from pprint import pprint
from optparse import OptionParser
from itertools import *
from rdflib.util import first
from FuXi.Rete.Util import selective_memoize
from FuXi.Syntax.InfixOWL import *
from rdflib.Namespace import Namespace
from rdflib.Graph import Graph
from RectorSegmentationAlgorithm import FMA as FMA_NS
from rdflib import RDF, OWL, RDFS, Variable, URIRef
from rdflib.store import *

from pygraph.classes.graph import graph as PyGraph
from pygraph.classes.digraph import digraph
from pygraph.algorithms.searching import breadth_first_search
from pygraph.readwrite.dot import write

CPRNS    = Namespace("http://purl.org/cpr/0.9#")
CPR      = ClassNamespaceFactory(CPRNS)
RO       = Namespace('http://purl.org/obo/owl/obo#')
MAP_NS   = Namespace('http://code.google.com/p/python-dlp/wiki/ClinicalOntologyModules#')
MAP      = ClassNamespaceFactory(MAP_NS)
FMA      = Namespace('http://purl.org/obo/owl/FMA#')
SNOMEDCT = Namespace('tag:info@ihtsdo.org,2007-07-31:SNOMED-CT#')
RIP      = Namespace('tag@case.edu,2009:DeductiveFeatureConstruction#')
SKOS     = Namespace('http://www.w3.org/2004/02/skos/core#')

def unfoldNestedDisjunct(cls):
    if isinstance(cls,BooleanClass):
        for t in cls:
            for _t in unfoldNestedDisjunct(CastClass(Class(t))):
                yield _t
    elif isinstance(cls,Restriction):
        assert cls.onProperty == RO['part_of']
        yield FMARestrictionQuery(cls.someValuesFrom)
    else:
        yield cls

RESTRICTION_QUERY1=\
"""
SELECT ?CLS 
{ 
    ?CLS rdfs:subClassOf 
      [ owl:onProperty ro:part_of;
        owl:someValuesFrom ?FILLER ]
}"""

RESTRICTION_QUERY2=\
"""
SELECT ?CLS 
{ 
    ?FILLER rdfs:subClassOf 
      [ owl:onProperty ro:has_part;
        owl:someValuesFrom ?CLS ]  
}"""


@selective_memoize([0])
def PClassTransitiveTraversal(uri,origFMAGraph):
    return [term for term in FMARestrictionQuery(uri)(
                                  origFMAGraph,
                                  outLinks=False)]

class FMARestrictionQuery(object):
    def __init__(self, cls):
        self.cls = classOrIdentifier(cls)
        self.emptyGraph = Graph()
        
    def __repr__(self):
        return ".. all parts of %s .."%self.emptyGraph.qname(self.cls)
    
    def __hash__(self):
        return hash(self.cls)

    def __eq__(self, other):
        return self.cls == other.cls    

    def __call__(self,graph,outLinks=True,inLinks=True):
        if inLinks:
            for rt in graph.query(RESTRICTION_QUERY1,
                                  initBindings={Variable('FILLER'):
                                                self.cls},
                                  initNs={u'ro':RO}):
                yield rt
        if outLinks:
            for rt in graph.query(RESTRICTION_QUERY2,
                                  initBindings={Variable('FILLER'):
                                                self.cls},
                                  initNs={u'ro':RO}):
                yield rt
            
def classDescriptionLinks(children,
                          roles=[CPRNS.actsOn,
                                 CPRNS.findingSite]):
    def stupidAssLambda(term):
        if isinstance(term,Individual):
            termId = term.identifier
        else:
            termId = term
            term = Individual(term)
        return OWL.Restriction in term.type and \
                             first(Individual.factoryGraph.objects(
                                     termId,
                                     OWL.onProperty)) in roles    
    for roleLinks in ifilter(stupidAssLambda,children):
        #a domain-specific procedure
        filler = first(Individual.factoryGraph.objects(
                               classOrIdentifier(roleLinks),
                               OWL.someValuesFrom))
        for term in unfoldNestedDisjunct(CastClass(Class(filler))):
            yield term

def extractAnatomy(cl):
    cl=CastClass(Class(cl,skipOWLClassMembership=True))
    if cl.identifier.find(FMA)+1:
        yield cl
    else:
        if isinstance(cl,BooleanClass):
            _list = [i for i in cl]
        else:
            _list = [i for i in cl.subClassOf]
        for roleLinks in classDescriptionLinks(_list):
            yield roleLinks
        
partOf = RO['part_of']        
            
def mintNodeLabel(cls,sncGraph,fmaGraph):
    if cls.identifier.find(FMA)+1:
        return first(fmaGraph.objects(cls.identifier,
                                      RDFS.label))
    else:
        if cls.qname:
            return cls.qname.split(':')[-1]
        elif isinstance(cls,Identifier):
            return cls.graph.qname(cls.identifier).split(':')[-1]
        else:
            return cls.identifier 

OBSERVED_ANAT_RIP_NODE_TYPE = 0
CA_RIP_NODE_TYPE            = 1
ANON_RIP_NODE_TYPE          = 2
NORMAL_RIP_NODE_TYPE        = 3

RIP_NODE_TYPE_URI_MAP = {
  OBSERVED_ANAT_RIP_NODE_TYPE : 'ObservedAnatomy',
  CA_RIP_NODE_TYPE            : 'CommonAncestor',
  NORMAL_RIP_NODE_TYPE        : 'RIPNode',
  ANON_RIP_NODE_TYPE          : 'RIPNode',
}

RIP_TYPES = [RIP[i] for i in set(RIP_NODE_TYPE_URI_MAP.values())]

def AddEdge(vizGraph,rdfGraph,start,startLabel,end,endLabel,updateDot=False):
    edge = (classOrIdentifier(start),RIP.containedBy,classOrIdentifier(end)) 
    if edge not in rdfGraph:
        if updateDot:
            vizGraph.add_edge((startLabel,endLabel))
        rdfGraph.add(edge)
        
def ExtractDot(rdfGraph,vizGraph):
    for node,p,o in ripGraph.triples_choices(
                                 (None,
                                  RDF.type,
                                  RIP_TYPES)):
        pass    

def AddNode(vizGraph,rdfGraph,label,term,_type=NORMAL_RIP_NODE_TYPE, updateDot=False):
    attrs = []
    classUri = RIP[RIP_NODE_TYPE_URI_MAP[_type]]
    if (term.identifier,RDF.type,classUri) not in rdfGraph:
        if _type == OBSERVED_ANAT_RIP_NODE_TYPE:
            attrs.append(('peripheries','3'))
        elif _type == CA_RIP_NODE_TYPE:
            attrs.append(('color','red'))
        elif _type == ANON_RIP_NODE_TYPE:
            attrs.append(('label',''))
    if not first(rdfGraph.triples_choices((term.identifier,RDF.type,RIP_TYPES))):
        if updateDot:
            vizGraph.add_node(label,attrs)
        rdfGraph.add((term.identifier,RDFS.label,Literal(label)))
    elif updateDot:
        for attr in attrs:
            vizGraph.add_node_attribute(label,attr)
    triple = (term.identifier,
              RDF.type,
              classUri)
    if triple not in rdfGraph:
        rdfGraph.add(triple)
                
def LowestCommonFMAAncestors(locusMap,fmaGraph, snctGraph, vizGraph):
    #subsumerMap / coverage : Aanc  -> [ Afma1, Afma2, ..., AfmaN ]
    #CA                     : Afma -> [ commonAncestor1, commonAncestor2, ... ] 
    coverage  = {}
    ca        = {}    
    terms     = set()
    labelToId = {}
    RIPGraph  = Graph()
    RIPGraph.bind('rip',RIP)
    RIPGraph.bind('rdfs',RDFS.RDFSNS)
    def LocusPropagationTraversal(node,graph):
        """
        node  - an FuXi.Syntax.InfixOWL.Class instance
        graph - an RDF graph
        
        (Transitively) traverses from the leaves towards the root of a 
        right identity axiom spanning tree 
        (for procedure and disease mechanism inferences). 
        Formed from an OWL / RDF graph of clinical medicine (via SNOMED-CT and FMA)
        
        """
        if node.identifier.find(FMA)+1:
            node.graph = fmaGraph
            if node.identifier == FMA['FMA_61775']:
                return
            #An FMA term - strict EL, and we are only concerned
            #with atomic concept inclusion and GCIs with 
            #existential role restrictions
            #Note: all FMA terms are interpreted WRT the FMA
            #OWL/RDF graph
            #assert node.isPrimitive()
            for parent in node.subClassOf:
                if OWL.Restriction in parent.type:
                    if (parent.identifier,
                        OWL.onProperty,
                        partOf) in graph:
                        parent = Restriction(partOf,
                                             fmaGraph,
                                             someValuesFrom='..',
                                             identifier=parent.identifier)
                        cls = Class(parent.restrictionRange,
                                    skipOWLClassMembership=True)
                        cls.prior = node
                        yield cls
                elif parent.identifier.find(FMA)+1:
                    parent.prior = node
                    yield parent
        else:
            #In O'snct-fma
            node = CastClass(node)
            if isinstance(node,BooleanClass):
                _list = [i for i in node]
            else:
                _list = [i for i in node.subClassOf]
            for parent in _list:
                parent = Class(classOrIdentifier(parent),
                               skipOWLClassMembership=True,
                               graph=classOrIdentifier(parent).find(FMA)+1 and \
                               fmaGraph or node.graph)
                if OWL.Restriction in parent.type:
                    if (parent.identifier,
                        OWL.onProperty,
                        partOf) in node.graph:
                        parent = Restriction(partOf,
                                             node.graph,
                                             someValuesFrom='..',
                                             identifier=parent.identifier)
                        link = parent.restrictionRange
                        cls = Class(link,
                                    skipOWLClassMembership=True,
                                    graph=link.find(FMA)+1 and fmaGraph or \
                                    node.graph)
                        cls.prior = node
                        yield cls
                else:
                    cls = Class(classOrIdentifier(parent),
                                skipOWLClassMembership=True,
                                graph=classOrIdentifier(parent).find(FMA)+1 and \
                                fmaGraph or graph)
                    cls.prior = node
                    yield  cls
    for cl,places in locusMap.items():
        assert isinstance(cl,URIRef)        
#        cls=Class(cl,graph=snctGraph)
#        assert not isinstance(cl,BNode),cls.__repr__(True)
        for fmaTerm in places:
            #For every
            if isinstance(fmaTerm,FMARestrictionQuery):
                for fmaTerm in fmaTerm(fmaGraph):
                    terms.add(Class(fmaTerm,
                                    skipOWLClassMembership=True,
                                    graph=fmaGraph))
                    RIPGraph.add((cl,
                                  RIP.locus,
                                  classOrIdentifier(fmaTerm)))                    
            else:
                terms.add(fmaTerm)
                RIPGraph.add((cl,
                              RIP.locus,
                              classOrIdentifier(fmaTerm)))
                
    for term in terms:
        leafLabel = mintNodeLabel(term,snctGraph,fmaGraph)
        AddNode(vizGraph,
                RIPGraph,
                leafLabel,
                term,
                OBSERVED_ANAT_RIP_NODE_TYPE)
        termId = classOrIdentifier(term)
        ontGraph = termId.find(FMA)+1 and fmaGraph or snctGraph
        #For each possibly observed anatomical sites
        term = Class(classOrIdentifier(term),
                     skipOWLClassMembership=True,
                     graph=ontGraph)
        def isSibling(_term):
            if _term == termId:
                return False
            _term = Class(_term,
                          skipOWLClassMembership=True,
                          graph=ontGraph)
            return _term in terms and termId not in coverage.get(_term,set())  
        commonSiblings = set()
        for ancestor in term.graph.transitiveClosure(LocusPropagationTraversal,
                                                     term):
            ancLabel    = mintNodeLabel(ancestor,snctGraph,fmaGraph)
            #update subsumer map

            coverage.setdefault(ancestor.identifier,
                                set()).add(term.identifier)
            #Is the original term a new member of the subsumer set for the ancestor?
            #If so, the ancestor is an LCA for all the terms subsumed by the ancestor
            #First we get all the (prior) terms subsumed by this ancestor that are
            #observed anatomy kinds 
            siblings = set(ifilter(isSibling,
                                   coverage.get(ancestor.identifier,set())))
            _type = NORMAL_RIP_NODE_TYPE
            #if siblings and not siblings.intersection(commonSiblings) and \
            if siblings and ancestor not in terms:
                #This is a (new) common anatomy ancestor of another
                #observed entity for and is not itself an observed entity
                commonSiblings.update(siblings)
                ca.setdefault(term.identifier,
                               set()).add(ancestor.identifier)
                _type = CA_RIP_NODE_TYPE
            if isinstance(ancestor.identifier,BNode):
                assert _type != CA_RIP_NODE_TYPE
                _type = ANON_RIP_NODE_TYPE
            priorLabel = mintNodeLabel(ancestor.prior,snctGraph,fmaGraph)
            AddNode(vizGraph,RIPGraph,ancLabel,ancestor,_type)
            AddEdge(vizGraph,
                    RIPGraph,
                    ancestor.prior,
                    priorLabel,
                    ancestor,
                    ancLabel)
    return RIPGraph, coverage
            
def LocalCommonAncestor(digraph,ca, coverage, labelToId, observedAnatomy): 
    for anatTerm in observedAnatomy:
        pass

UNOBSERVED_LEAF_QUERY=\
"""
SELECT ?NODE1 ?NODE
{
  ?NODE1 rip:containedBy ?NODE
  OPTIONAL {
    ?NODE rip:containedBy ?OTHER; 
  }
  FILTER(!BOUND(?OTHER))
}
"""
@selective_memoize([0,1])   
def FlowPathTraversal(node,path,hubs,graph):
    _path = [p for p in path]
    for parent in graph.objects(node,RIP.containedBy):
        _path.append(parent)
        if parent in hubs:
            yield _path
        for continuedPath in FlowPathTraversal(parent, _path, hubs, graph):
            yield continuedPath
   
def CircumscriptionMapping(observedVariables,anatomyHubs,ripGraph):
    varsToHub = {}
    hubToVars = {}
    for obsAnat in observedVariables:
        for path in FlowPathTraversal(obsAnat, [], anatomyHubs, ripGraph):
            hub = path[-1]
            varsToHub.setdefault(obsAnat,set()).add(hub) 
            hubToVars.setdefault(hub    ,set()).add(obsAnat)
    return varsToHub,hubToVars
    
def main():
    from optparse import OptionParser
    parser = OptionParser()
    parser.add_option('--anatomy',type="choice",default='all',
      choices=['all','given'],
      help='')
    parser.add_option('--action',type="choice",default='createRIP',
      choices=['createRIP','vizualize'],
      help='')    
    parser.add_option('--file','-f',
      help='')    
    parser.add_option('--class',
                  dest='classes',
                  action='append',
                  default=[],
                  metavar='URI',
                  help='')     
    (options, args) = parser.parse_args()
    
    if options.action == 'vizualize':
        ripGraph = Graph.parse(open(options.file+'.n3'),format='n3')
        for node,p,o in ripGraph.triples_choices(
                                     (None,
                                      RDF.type,
                                      RIP_TYPES)):
            pass
        if len(args)>2:
            varMapGraph = Graph().parse(args[2])
            terms = set(varMapGraph.subjects(SKOS.altSymbol))
            graph += varMapGraph
        ripGraphFile = open(options.file+'.n3','w')
        ripGraphFile.write(ripGraph.serialize(format='n3'))
            
    else:    
        vizGraph = digraph()
        graph = Graph().parse(args[0])
        Individual.factoryGraph = graph
        
        locusMap = {}
        if options.anatomy == 'given':
            terms = set([URIRef(term) for term in options.classes]) 
        else:
            terms = set(MAP['SNOMED-term'].subSumpteeIds())
        varMapGraph = None
        if len(args)>2:
            varMapGraph = Graph().parse(args[2])
            terms = set(varMapGraph.subjects(SKOS.altSymbol))
            graph += varMapGraph
        for cl in terms:
            querySet = set()
            clsSet   = set()
            for i in extractAnatomy(cl):
                if isinstance(i,Class):
                    clsSet.add(i)
                else:
                    querySet.add(i)
            locusMap[cl]=[i for i in chain(querySet,clsSet)]

        pprint(locusMap)
    
        store = plugin.get('MySQL',Store)('fma')
        rt=store.open('user=root,password=,host=localhost,db=fma',
                      create=False)
        #fmaGraph = Graph(store,URIRef(FMA))
        fmaGraph = Graph().parse(args[1])
    
        ripGraph,coverage = LowestCommonFMAAncestors(locusMap, 
                                                     fmaGraph, 
                                                     graph,
                                                     vizGraph)
        nodes = set()
        nodeTypeMap = {}
        for s,p,o in ripGraph.triples_choices((None,RDF.type,RIP_TYPES)):        
            nodeTypeMap.setdefault(s,set()).add(o)
        for node,types in nodeTypeMap.items():
            if (node,None,None) in ripGraph or (None,None,node) in ripGraph:
                label = first(ripGraph.objects(node,RDFS.label))
                attrs = []
                if RIP[RIP_NODE_TYPE_URI_MAP[OBSERVED_ANAT_RIP_NODE_TYPE]] in types:
                    attrs.append(('peripheries','3'))
                    attrs.append(('shape','circle'))
                if RIP[RIP_NODE_TYPE_URI_MAP[CA_RIP_NODE_TYPE]] in types:
                    attrs.append(('color','red'))
                    attrs.append(('shape','circle'))
                if RIP[RIP_NODE_TYPE_URI_MAP[OBSERVED_ANAT_RIP_NODE_TYPE]] not in types and \
                   RIP[RIP_NODE_TYPE_URI_MAP[CA_RIP_NODE_TYPE]] in types:
                    attrs.append(('shape','plaintext'))
                if isinstance(node,BNode):
                    attrs.append(('label',''))
                else:
                    attrs.append(('label','\n'.join(label.split('\n'))))
                vizGraph.add_node(label,attrs)
        toDo = []
        for s,o in ripGraph.query(UNOBSERVED_LEAF_QUERY,
                                  initNs={u'rip':RIP}):
            if RIP.ObservedAnatomy not in ripGraph.objects(o,RDF.type):
                toDo.append((s,o))
        for s,o in toDo:
            ripGraph.remove((s,None,o))
        for s,p,o in ripGraph.triples((None,RIP.containedBy,None)):
            startLabel = first(ripGraph.objects(s,RDFS.label)) 
            endLabel   = first(ripGraph.objects(o,RDFS.label))
            vizGraph.add_edge((startLabel,endLabel))
        ripGraphFile = open(options.file+'.n3','w')
        ripGraphFile.write(ripGraph.serialize(format='n3'))
        ripGrapVizFile = open(options.file+'.dot','w')
        ripGrapVizFile.write(write(vizGraph))

if __name__ == '__main__':
    main()
