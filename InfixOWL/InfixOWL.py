#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
RDFLib Python binding for OWL Abstract Syntax

see: http://www.w3.org/TR/owl-semantics/syntax.html
     http://owl-workshop.man.ac.uk/acceptedLong/submission_9.pdf

3.2.3 Axioms for complete classes without using owl:equivalentClass

  Named class description of type 2 (with owl:oneOf) or type 4-6 (with owl:intersectionOf, owl:unionOf or owl:complementOf
  
Uses Manchester Syntax for __repr__  

>>> exNs = Namespace('http://example.com/')        
>>> namespace_manager = NamespaceManager(Graph())
>>> namespace_manager.bind('ex', exNs, override=False)
>>> namespace_manager.bind('owl', OWL_NS, override=False)
>>> g = Graph()    
>>> g.namespace_manager = namespace_manager

Now we have an empty graph, we can construct OWL classes in it
using the Python classes defined in this module

>>> a = Class(exNs.Opera,graph=g)

Now we can assert rdfs:subClassOf and owl:equivalentClass relationships 
(in the underlying graph) with other classes using the 'subClassOf' 
and 'equivalentClass' descriptors which can be set to a list
of objects for the corresponding predicates.

>>> a.subClassOf = [exNs.MusicalWork]

We can then access the rdfs:subClassOf relationships

>>> print list(a.subClassOf)
[Class: ex:MusicalWork ]

This can also be used against already populated graphs:

#>>> owlGraph = Graph().parse(OWL_NS)
#>>> namespace_manager.bind('owl', OWL_NS, override=False)
#>>> owlGraph.namespace_manager = namespace_manager
#>>> list(Class(OWL_NS.Class,graph=owlGraph).subClassOf)
#[Class: rdfs:Class ]

Operators are also available.  For instance we can add ex:Opera to the extension
of the ex:CreativeWork class via the '+=' operator

>>> a
Class: ex:Opera SubClassOf: ex:MusicalWork
>>> b = Class(exNs.CreativeWork,graph=g)
>>> b += a
>>> print list(a.subClassOf)
[Class: ex:CreativeWork , Class: ex:MusicalWork ]

And we can then remove it from the extension as well

>>> b -= a
>>> a
Class: ex:Opera SubClassOf: ex:MusicalWork

Boolean class constructions can also  be created with Python operators
For example, The | operator can be used to construct a class consisting of a owl:unionOf 
the operands:

>>> c =  a | b | Class(exNs.Work,graph=g)
>>> c
( ex:Opera or ex:CreativeWork or ex:Work )

Boolean class expressions can also be operated as lists (using python list operators)

>>> del c[c.index(Class(exNs.Work,graph=g))]
>>> c
( ex:Opera or ex:CreativeWork )

The '&' operator can be used to construct class intersection:
      
>>> woman = Class(exNs.Female,graph=g) & Class(exNs.Human,graph=g)
>>> woman.identifier = exNs.Woman
>>> woman
( ex:Female and ex:Human )

Enumerated classes can also be manipulated

>>> contList = [Class(exNs.Africa,graph=g),Class(exNs.NorthAmerica,graph=g)]
>>> EnumeratedClass(members=contList,graph=g)
{ ex:Africa ex:NorthAmerica }

owl:Restrictions can also be instanciated:

>>> Restriction(exNs.hasParent,graph=g,allValuesFrom=exNs.Human)
( ex:hasParent only ex:Human )

Restrictions can also be created using Manchester OWL syntax in 'colloquial' Python 
>>> exNs.hasParent |some| Class(exNs.Physician,graph=g)
( ex:hasParent some ex:Physician )

>>> Property(exNs.hasParent,graph=g) |max| Literal(1)
( ex:hasParent max 1 )

#>>> print g.serialize(format='pretty-xml')

"""
import os
from pprint import pprint
from rdflib import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,BNode,Literal,Variable
from rdflib.store import Store
from rdflib.Graph import Graph
from rdflib.Collection import Collection
from rdflib.syntax.NamespaceManager import NamespaceManager
from infix import *

OWL_NS = Namespace("http://www.w3.org/2002/07/owl#")

nsBinds = {
    'skos': 'http://www.w3.org/2004/02/skos/core#',
    'rdf' : RDF.RDFNS,
    'rdfs': RDFS.RDFSNS,
    'owl' : OWL_NS,       
    'dc'  : "http://purl.org/dc/elements/1.1/",
}

def generateQName(graph,uri):
    prefix,uri,localName = graph.compute_qname(classOrIdentifier(uri)) 
    return u':'.join([prefix,localName])    

def classOrTerm(thing):
    if isinstance(thing,Class):
        return thing.identifier
    else:
        assert isinstance(thing,(URIRef,BNode,Literal))
        return thing

def classOrIdentifier(thing):
    if isinstance(thing,Class):
        return thing.identifier
    else:
        assert isinstance(thing,(URIRef,BNode))
        return thing

def propertyOrIdentifier(thing):
    if isinstance(thing,Property):
        return thing.identifier
    else:
        assert isinstance(thing,URIRef)
        return thing

def manchesterSyntax(thing,store,boolean=None,transientList=False):
    """
    Used for http://code.google.com/p/python-dlp/wiki/SemanticWebOntologyPublisher
    """
    assert thing is not None
    if boolean:
        if transientList:
            children = [manchesterSyntax(child,store) for child in thing ]
        else:
            children = [manchesterSyntax(child,store) for child in Collection(store,thing)]
        if boolean == OWL_NS.intersectionOf:
            return '( '+ ' and '.join(children) + ' )'
        elif boolean == OWL_NS.unionOf:
            return '( '+ ' or '.join(children) + ' )'
        elif boolean == OWL_NS.oneOf:
            return '{ '+ ' '.join(children) +' }'
        else:            
            assert boolean == OWL_NS.complementOf
    elif OWL_NS.Restriction in store.objects(subject=thing, predicate=RDF.type):
        prop = list(store.objects(subject=thing, predicate=OWL_NS.onProperty))[0]
        prefix,uri,localName = store.compute_qname(prop)
        propString = u':'.join([prefix,localName])
        for onlyClass in store.objects(subject=thing, predicate=OWL_NS.allValuesFrom):
            return '( %s only %s )'%(propString,manchesterSyntax(onlyClass,store))
        for someClass in store.objects(subject=thing, predicate=OWL_NS.someValuesFrom):    
            return '( %s some %s )'%(propString,manchesterSyntax(someClass,store))
        cardLookup = {OWL_NS.maxCardinality:'max',OWL_NS.minCardinality:'min',OWL_NS.cardinality:'equals'}
        for s,p,o in store.triples_choices((thing,cardLookup.keys(),None)):            
            return '( %s %s %s )'%(propString,cardLookup[p],o.encode('utf-8'))
    compl = list(store.objects(subject=thing, predicate=OWL_NS.complementOf)) 
    if compl:
        return '( not %s )'%(manchesterSyntax(compl[0],store))
    else:
        for boolProp,col in store.query("SELECT ?p ?bool WHERE { ?class a owl:Class; ?p ?bool . ?bool rdf:first ?foo }",
                                         initBindings={Variable("?class"):thing},
                                         initNs=nsBinds):
            if not isinstance(thing,URIRef):                
                return manchesterSyntax(col,store,boolean=boolProp)
        try:
            prefix,uri,localName = store.compute_qname(thing) 
            qname = u':'.join([prefix,localName])
        except Exception,e:
            print list(store.objects(subject=thing,predicate=RDF.type))
            raise
            return '[]'#+thing._id.encode('utf-8')+'</em>'            
        if (thing,RDF.type,OWL_NS.Class) not in store:
            return qname.encode('utf-8')
        else:
            return qname.encode('utf-8')

class Class(object):
    """
    'General form' for classes:
    
    The Manchester Syntax (supported in Protege) is used as the basis for the form 
    of this class
    
    See: http://owl-workshop.man.ac.uk/acceptedLong/submission_9.pdf:
    
    ‘Class:’ classID {Annotation
                  ( (‘SubClassOf:’ ClassExpression)
                  | (‘EquivalentTo’ ClassExpression)
                  | (’DisjointWith’ ClassExpression)) }
    
    Appropriate excerpts from OWL Reference:
    
    ".. Subclass axioms provide us with partial definitions: they represent 
     necessary but not sufficient conditions for establishing class 
     membership of an individual."
     
   ".. A class axiom may contain (multiple) owl:equivalentClass statements"   
                  
    "..A class axiom may also contain (multiple) owl:disjointWith statements.."
    
    "..An owl:complementOf property links a class to precisely one class 
      description."
      
    """
    factoryGraph = Graph()
    def __init__(self, identifier=BNode(),subClassOf=None,equivalentClass=None,
                       disjointWith=None,complementOf=None,graph=None,skipOWLClassMembership = False):
        self.__identifier = identifier
        self.qname = None
        self.graph = graph or self.factoryGraph
        if not isinstance(identifier,BNode):
            prefix,uri,localName = self.graph.compute_qname(identifier) 
            self.qname = u':'.join([prefix,localName])
        if not skipOWLClassMembership and (self.identifier,RDF.type,OWL_NS.Class) not in self.graph:
            self.graph.add((self.identifier,RDF.type,OWL_NS.Class))
        
        self.subClassOf      = subClassOf 
        self.equivalentClass = equivalentClass
        self.disjointWith    = disjointWith  
        self.complementOf    = complementOf

    def _get_identifier(self):
        return self.__identifier
    def _set_identifier(self, i):
        assert i
        if i != self.__identifier:
            oldStmtsOut = [(p,o) for s,p,o in self.graph.triples((self.__identifier,None,None))]
            oldStmtsIn  = [(s,p) for s,p,o in self.graph.triples((None,None,self.__identifier))]
            for p1,o1 in oldStmtsOut:                
                self.graph.remove((self.__identifier,p1,o1))
            for s1,p1 in oldStmtsIn:                
                self.graph.remove((s1,p1,self.__identifier))
            self.__identifier = i
            self.graph.addN([(i,p1,o1,self.graph) for p1,o1 in oldStmtsOut])
            self.graph.addN([(s1,p1,i,self.graph) for s1,p1 in oldStmtsIn])
    identifier = property(_get_identifier, _set_identifier)
    def __iadd__(self, other):
        assert isinstance(other,Class)
        other.subClassOf = [self]
        return self

    def __isub__(self, other):
        assert isinstance(other,Class)
        self.graph.remove((classOrIdentifier(other),RDFS.subClassOf,self.identifier))
        return self

    def __or__(self,other):
        """
        Construct an anonymous class description consisting of the union of this class and '
        other' and return it
        """
        return BooleanClass(operator=OWL_NS.unionOf,members=[self,other],graph=self.graph)

    def __and__(self,other):
        """
        Construct an anonymous class description consisting of the intersection of this class and '
        other' and return it
        """
        return BooleanClass(operator=OWL_NS.intersectionOf,members=[self,other],graph=self.graph)
            
    def _get_subClassOf(self):
        for anc in self.graph.objects(subject=self.identifier,predicate=RDFS.subClassOf):
            yield Class(anc,graph=self.graph)
    def _set_subClassOf(self, other):
        if not other:
            return        
        for sc in other:
            self.graph.add((self.identifier,RDFS.subClassOf,classOrIdentifier(sc)))
    subClassOf = property(_get_subClassOf, _set_subClassOf)

    def _get_equivalentClass(self):
        for ec in self.graph.objects(subject=self.identifier,predicate=OWL_NS.equivalentClass):
            yield Class(ec,graph=self.graph)
    def _set_equivalentClass(self, other):
        if not other:
            return
        for sc in other:
            self.graph.add((self.identifier,OWL_NS.equivalentClass,classOrIdentifier(sc)))
    equivalentClass = property(_get_equivalentClass, _set_equivalentClass)

    def _get_disjointWith(self):
        for dc in self.graph.objects(subject=self.identifier,predicate=OWL_NS.disjointWith):
            yield Class(dc,graph=self.graph)
    def _set_disjointWith(self, other):
        if not other:
            return
        for c in other:
            self.graph.add((self.identifier,OWL_NS.disjointWith,classOrIdentifier(c)))
    disjointWith = property(_get_disjointWith, _set_disjointWith)

    def _get_complementOf(self):
        comp = list(self.graph.objects(subject=self.identifier,predicate=OWL_NS.complementOf))
        if not comp:
            return None
        elif len(comp) == 1:
            return Class(comp[0],graph=self.graph)
        else:
            raise Exception(len(comp))
        
    def _set_complementOf(self, other):
        if not other:
            return
        self.graph.add((self.identifier,OWL_NS.complementOf,classOrIdentifier(other)))
    complementOf = property(_get_complementOf, _set_complementOf)
    
#    def __str__(self):
#        return str(self.identifier)

    def __repr__(self,full=False,normalization=True):
        """
        Returns the Manchester Syntax equivalent for this class
        """
        exprs = []
        sc = list(self.subClassOf)
        ec = list(self.equivalentClass)
        for boolClass,p,rdfList in self.graph.triples_choices((self.identifier,
                                                               [OWL_NS.intersectionOf,
                                                                OWL_NS.unionOf],
                                                                None)):
            ec.append(manchesterSyntax(rdfList,self.graph,boolean=p))
        dc = list(self.disjointWith)
        c  = self.complementOf
        klassKind = ''
        label = list(self.graph.objects(self.identifier,RDFS.label))
        label = label and '('+label[0]+')' or ''
        if sc:
            if full:
                scJoin = '\n                '
            else:
                scJoin = ', '
            necStatements = [
              isinstance(s,Class) and isinstance(self.identifier,BNode) and
                                      repr(BooleanClass(classOrIdentifier(s),
                                                        operator=None,
                                                        graph=self.graph)) or 
              manchesterSyntax(classOrIdentifier(s),self.graph) for s in sc]
            if necStatements:
                klassKind = "Primitive Type %s"%label
            exprs.append("SubClassOf: %s"%scJoin.join(necStatements))
            if full:
                exprs[-1]="\n    "+exprs[-1]
        if ec:
            nec_SuffStatements = [    
              isinstance(s,basestring) and s or 
              manchesterSyntax(classOrIdentifier(s),self.graph) for s in ec]
            if nec_SuffStatements:
                klassKind = "A Defined Class %s"%label
            exprs.append("EquivalentTo: %s"%', '.join(nec_SuffStatements))
            if full:
                exprs[-1]="\n    "+exprs[-1]
        if dc:
            if c:
                dc.append(c)
            exprs.append("DisjointWith %s\n"%'\n                 '.join([
              manchesterSyntax(classOrIdentifier(s),self.graph) for s in dc]))
            if full:
                exprs[-1]="\n    "+exprs[-1]
        descr = list(self.graph.objects(self.identifier,RDFS.comment))
        if full and normalization:
            klassDescr = klassKind and '\n    ## %s ##'%klassKind +\
            (descr and "\n    %s"%descr[0] or '') + ' . '.join(exprs) or ' . '.join(exprs)
        else:
            klassDescr = full and (descr and "\n    %s"%descr[0] or '') or '' + ' . '.join(exprs)
        return "Class: %s "%(isinstance(self.identifier,BNode) and '[]' or self.qname)+klassDescr

class OWLRDFListProxy(object):
    def __init__(self,rdfList,members=None,graph=Graph()):
        members = members and members or []
        if rdfList:
            self._rdfList = Collection(graph,rdfList[0])
            for member in members:
                if member not in self._rdfList:
                    self._rdfList.append(classOrIdentifier(member))
        else:
            self._rdfList = Collection(self.graph,BNode(),
                                       [classOrIdentifier(m) for m in members])
            self.graph.add((self.identifier,self._operator,self._rdfList.uri)) 

    #Redirect python list accessors to the underlying Collection instance
    def __len__(self):
        return len(self._rdfList)

    def index(self, item):
        return self._rdfList.index(classOrIdentifier(item))
    
    def __getitem__(self, key):
        return self._rdfList[key]

    def __setitem__(self, key, value):
        self._rdfList[key] = classOrIdentifier(value)
        
    def __delitem__(self, key):
        del self._rdfList[key]        

    def __iter__(self):
        for item in self._rdfList:
            yield item

    def __contains__(self, item):
        for i in self._rdfList:
            if i == classOrIdentifier(item):
                return 1
        return 0

    def __iadd__(self, other):
        self._rdfList.append(classOrIdentifier(other))

class EnumeratedClass(Class,OWLRDFListProxy):
    """
    Class for owl:oneOf forms:
    
    OWL Abstract Syntax is used
    
    axiom ::= 'EnumeratedClass(' classID ['Deprecated'] { annotation } { individualID } ')'    
    """
    _operator = OWL_NS.oneOf
    def __init__(self, identifier=BNode(),members=None,graph=Graph()):
        Class.__init__(self,identifier,graph = graph)
        members = members and members or []
        rdfList = list(self.graph.objects(predicate=OWL_NS.oneOf,subject=self.identifier))
        OWLRDFListProxy.__init__(self, rdfList, members, graph = graph)
    def __repr__(self):
        """
        Returns the Manchester Syntax equivalent for this class
        """
        return manchesterSyntax(self._rdfList.uri,self.graph,boolean=self._operator)        

BooleanPredicates = [OWL_NS.intersectionOf,OWL_NS.unionOf]

class BooleanClass(Class,OWLRDFListProxy):
    """
    See: http://www.w3.org/TR/owl-ref/#Boolean
    
    owl:complementOf is an attribute of Class, however
    
    """
    def __init__(self,identifier=BNode(),operator=OWL_NS.intersectionOf,
                 members=None,graph=Graph()):
        if operator is None:
            for s,p,o in graph.triples_choices((identifier,
                                                [OWL_NS.intersectionOf,
                                                 OWL_NS.unionOf],
                                                 None)):
                operator = p
        Class.__init__(self,identifier,graph = graph)
        members = members and members or []
        assert operator in [OWL_NS.intersectionOf,OWL_NS.unionOf], str(operator)
        self._operator = operator
        rdfList = list(self.graph.objects(predicate=operator,subject=self.identifier))
        OWLRDFListProxy.__init__(self, rdfList, members, graph = graph)

    def __repr__(self):
        """
        Returns the Manchester Syntax equivalent for this class
        """
        return manchesterSyntax(self._rdfList.uri,self.graph,boolean=self._operator)

    def __or__(self,other):
        """
        Adds other to the list and returns self
        """
        assert self._operator == OWL_NS.unionOf
        self._rdfList.append(classOrIdentifier(other))
        return self

def AllDifferent(members):
    """
    DisjointClasses(' description description { description } ')'
    
    """
    pass

class Restriction(Class):
    """
    restriction ::= 'restriction(' datavaluedPropertyID dataRestrictionComponent 
                                 { dataRestrictionComponent } ')'
                  | 'restriction(' individualvaluedPropertyID 
                      individualRestrictionComponent 
                      { individualRestrictionComponent } ')'    
    """
    def __init__(self,onProperty,graph = Graph(),allValuesFrom=None,someValuesFrom=None,value=None,
                      cardinality=None,maxCardinality=None,minCardinality=None):
        super(Restriction, self).__init__(BNode(),graph=graph,skipOWLClassMembership=True)
        self.__prop = propertyOrIdentifier(onProperty)
        assert isinstance(self.__prop,URIRef) 
        self.graph.add((self.identifier,OWL_NS.onProperty,self.__prop))
        restrTypes = [
                      (allValuesFrom,OWL_NS.allValuesFrom ),
                      (someValuesFrom,OWL_NS.someValuesFrom),
                      (value,OWL_NS.hasValue),
                      (cardinality,OWL_NS.cardinality),
                      (maxCardinality,OWL_NS.maxCardinality),
                      (minCardinality,OWL_NS.minCardinality)]
        validRestrProps = [(i,oTerm) for (i,oTerm) in restrTypes if i] 
        assert len(validRestrProps) == 1
        for val,oTerm in validRestrProps:
            self.graph.add((self.identifier,oTerm,classOrTerm(val)))   
        if (self.identifier,RDF.type,OWL_NS.Restriction) not in self.graph:
            self.graph.add((self.identifier,RDF.type,OWL_NS.Restriction))
            
    def __repr__(self):
        """
        Returns the Manchester Syntax equivalent for this restriction
        """
        return manchesterSyntax(self.identifier,self.graph)

### Infix Operators ###

some     = Infix(lambda prop,_class: Restriction(prop,graph=_class.graph,someValuesFrom=_class))
only     = Infix(lambda prop,_class: Restriction(prop,graph=_class.graph,allValuesFrom=_class))
max      = Infix(lambda prop,_class: Restriction(prop,graph=prop.graph,maxCardinality=_class))
min      = Infix(lambda prop,_class: Restriction(prop,graph=prop.graph,minCardinality=_class))
exactly  = Infix(lambda prop,_class: Restriction(prop,graph=prop.graph,cardinality=_class))
value    = Infix(lambda prop,_class: Restriction(prop,graph=prop.graph,hasValue=_class))

class Property(object):
    """
    axiom ::= 'DatatypeProperty(' datavaluedPropertyID ['Deprecated'] { annotation } 
                { 'super(' datavaluedPropertyID ')'} ['Functional']
                { 'domain(' description ')' } { 'range(' dataRange ')' } ')'
            | 'ObjectProperty(' individualvaluedPropertyID ['Deprecated'] { annotation } 
                { 'super(' individualvaluedPropertyID ')' }
                [ 'inverseOf(' individualvaluedPropertyID ')' ] [ 'Symmetric' ] 
                [ 'Functional' | 'InverseFunctional' | 'Functional' 'InverseFunctional' |
                  'Transitive' ]
                { 'domain(' description ')' } { 'range(' description ')' } ')    
    """
    factoryGraph = Graph()
    def __init__(self,identifier=BNode(),graph = None,baseType=OWL_NS.ObjectProperty,
                      subPropertyOf=None,domain=None,range=None,inverseOf=None,
                      otherType=None,equivalentProperty=None):
        self.identifier = identifier
        self.graph = graph or self.factoryGraph        
    

def test():
    import doctest
    doctest.testmod()
    galenGraph = Graph()
    galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/SDB-local/Base/owl/DataNodes.owl'))
    #galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/Ontologies/bfo-1.0.owl'))
    #galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/Ontologies/OBI.owl'))
    #galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/Ontologies/problem-oriented-medical-record.owl'))
    #galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/Ontologies/InformationObjects.owl'))
    #galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/Ontologies/ExtendedDnS.owl'))
    #galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/Ontologies/DOLCE-Lite.owl'))
    #galenGraph.parse(os.path.join(os.path.dirname(__file__), '/home/chimezie/workspace/Ontologies/Plans.owl'))
    graph=galenGraph
    for c in graph.subjects(predicate=RDF.type,object=OWL_NS.Class):
        if isinstance(c,URIRef):
            print Class(c,graph=graph).__repr__(True),"\n"

if __name__ == '__main__':
    test()
