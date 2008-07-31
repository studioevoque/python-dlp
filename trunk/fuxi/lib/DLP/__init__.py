#!/usr/local/bin/python
# -*- coding: utf-8 -*-
"""
This module implements a Description Horn Logic implementation as defined
by Grosof, B. et.al. ("Description Logic Programs: Combining Logic Programs with 
Description Logic" [1]) in section 4.4.  As such, it implements recursive mapping
functions "T", "Th" and "Tb" which result in "custom" (dynamic) rulesets, RIF Basic 
Logic Dialect: Horn rulesets [2], [3].  The rulesets are evaluated against an 
efficient RETE-UL network.

It is a Description Logic Programming [1] Implementation on top of RETE-UL:

"A DLP is directly defined as the LP-correspondent of a def-Horn
ruleset that results from applying the mapping T ."

The mapping is as follows:

== Core (Description Horn Logic) ==

Th(A,x)                      -> A(x)
Th((C1 ^ C2 ^ ... ^ Cn),x)   -> Th(C1,x) ^ Th(C2,x) ^ ... ^ Th(Cn,x) 
Th((‚àÄR.C),x)                 -> Th(C(y)) :- R(x,y)
Tb(A(x))                     -> A(x)
Tb((C1 ^ C2 ^ ... ^ Cn),x)   -> Tb(C1,x) ^ Tb(C2,x) ^ ... ^ Tb(Cn,x)
Tb((C1 v C2 v ... v Cn),x)   -> Tb(C1,x) v Tb(C2,x) v ... v Tb(Cn,x)
Tb((‚àÉR.C),x)                ->  R(x,y) ^ Tb(C,y) 

In addition, basic logic tautologies are included in the DHL definition:

(H ^ H0) :- B                 -> { H  :- B
                                   H0 :- B }
(H :- H0) :- B                -> H :- B ^ H0

H :- (B v B0)                 -> { H :- B
                                   H :- B0 }

== Class Equivalence ==

T(owl:equivalentClass(C,D)) -> { T(rdfs:subClassOf(C,D) 
                                 T(rdfs:subClassOf(D,C) }
                                 
== Domain and Range Axioms (Base Description Logic: "ALC") ==                                                                                                       

T(rdfs:range(P,D))  -> D(y) := P(x,y)
T(rdfs:domain(P,D)) -> D(x) := P(x,y)

== Property Axioms (Role constructors: "I") ==

T(rdfs:subPropertyOf(P,Q))     -> Q(x,y) :- P(x,y)
T(owl:equivalentProperty(P,Q)) -> { Q(x,y) :- P(x,y)
                                    P(x,y) :- Q(x,y) }
T(owl:inverseOf(P,Q))          -> { Q(x,y) :- P(y,x)
                                    P(y,x) :- Q(x,y) }
T(owl:TransitiveProperty(P))   -> P(x,z) :- P(x,y) ^ P(y,z)                                                                        

[1] http://www.cs.man.ac.uk/~horrocks/Publications/download/2003/p117-grosof.pdf
[2] http://www.w3.org/2005/rules/wg/wiki/Core/Positive_Conditions
[3] http://www.w3.org/2005/rules/wg/wiki/asn06

"""

from __future__ import generators
from sets import Set
from rdflib import BNode, RDF, Namespace, Variable, RDFS
from rdflib.util import first
from rdflib.Collection import Collection
from rdflib.store import Store,VALID_STORE, CORRUPTED_STORE, NO_STORE, UNKNOWN
from rdflib import Literal, URIRef
from pprint import pprint, pformat
import sys, copy
#from rdflib.term_utils import *
from rdflib.Graph import QuotedGraph, Graph
from rdflib.store.REGEXMatching import REGEXTerm, NATIVE_REGEX, PYTHON_REGEX
from FuXi.Rete.RuleStore import Formula
from FuXi.Rete.AlphaNode import AlphaNode
from FuXi.Horn.PositiveConditions import And, Or, Uniterm, Condition, Atomic,SetOperator,Exists
from FuXi.Horn.HornRules import Clause,Rule
from FuXi.Rete.Util import renderNetwork
from cStringIO import StringIO

non_DHL_OWL_Semantics=\
"""
@prefix log: <http://www.w3.org/2000/10/swap/log#>.
@prefix math: <http://www.w3.org/2000/10/swap/math#>.
@prefix owl: <http://www.w3.org/2002/07/owl#>.
@prefix xsd: <http://www.w3.org/2001/XMLSchema#>.
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix : <http://eulersharp.sourceforge.net/2003/03swap/owl-rules#>.
@prefix list: <http://www.w3.org/2000/10/swap/list#>.
#Additional OWL-compliant semantics, mappable to Production Rules 

#Subsumption (purely for TBOX classification)
{?C rdfs:subClassOf ?SC. ?A rdfs:subClassOf ?C} => {?A rdfs:subClassOf ?SC}.
{?C owl:equivalentClass ?A} => {?C rdfs:subClassOf ?A. ?A rdfs:subClassOf ?C}.
{?C rdfs:subClassOf ?SC. ?SC rdfs:subClassOf ?C} => {?C owl:equivalentClass ?SC}.

{?C owl:disjointWith ?B. ?M a ?C. ?Y a ?B } => {?M owl:differentFrom ?Y}.

{?P owl:inverseOf ?Q. ?P a owl:InverseFunctionalProperty} => {?Q a owl:FunctionalProperty}.
{?P owl:inverseOf ?Q. ?P a owl:FunctionalProperty} => {?Q a owl:InverseFunctionalProperty}.

#Inverse functional semantics
{?P a owl:FunctionalProperty. ?S ?P ?O. ?S ?P ?Y} => {?O = ?Y}.
{?P a owl:InverseFunctionalProperty. ?S ?P ?O. ?Y ?P ?O} => {?S = ?Y}.
{?T1 = ?T2. ?S = ?T1} => {?S = ?T2}.
{?T1 ?P ?O. ?T1 = ?T2.} => {?T2 ?P ?O}.

#For OWL/InverseFunctionalProperty/premises004
{?C owl:oneOf ?L. ?L rdf:first ?X; rdf:rest rdf:nil. ?P rdfs:domain ?C} => {?P a owl:InverseFunctionalProperty}.
#For OWL/InverseFunctionalProperty/premises004
{?C owl:oneOf ?L. ?L rdf:first ?X; rdf:rest rdf:nil. ?P rdfs:range ?C} => {?P a owl:FunctionalProperty}.

#For OWL/oneOf
{?C owl:oneOf ?L. ?X list:in ?L} => {?X a ?C}.
{?L rdf:first ?I} => {?I list:in ?L}.
{?L rdf:rest ?R. ?I list:in ?R} => {?I list:in ?L}.

{?P a owl:SymmetricProperty. ?S ?P ?O} => {?O ?P ?S}.
{?S owl:differentFrom ?O} => {?O owl:differentFrom ?S}.
{?S owl:complementOf ?O} => {?O owl:complementOf ?S}.
{?S owl:disjointWith ?O} => {?O owl:disjointWith ?S}.

"""

OWL_NS    = Namespace("http://www.w3.org/2002/07/owl#")

LOG = Namespace("http://www.w3.org/2000/10/swap/log#")
Any = None

LHS = 0
RHS = 1

def reduceAnd(left,right):
    if isinstance(left,And):
        left = reduce(reduceAnd,left)
    elif isinstance(right,And):
        right = reduce(reduceAnd,right)
    if isinstance(left,list) and not isinstance(right,list):
        return left+[right]
    elif isinstance(left,list) and isinstance(right,list):
        return left+right
    elif isinstance(left,list) and not isinstance(right,list):
        return left+[right]
    elif not isinstance(left,list) and isinstance(right,list):
        return [left]+right
    else:
        return [left,right]
    
def NormalizeClause(clause):
    def fetchFirst(gen):
        return first(gen)
    if hasattr(clause.head,'next') and not isinstance(clause.head,Condition):
        clause.head = fetchFirst(clause.head)
    if hasattr(clause.body,'next') and not isinstance(clause.body,Condition):
        clause.body = fetchFirst(clause.body)
#    assert isinstance(clause.head,(Atomic,And,Clause)),repr(clause.head)
#    assert isinstance(clause.body,Condition),repr(clause.body)
    if isinstance(clause.head,And):
        clause.head.formulae = reduce(reduceAnd,clause.head)
    if isinstance(clause.body,And):
        clause.body.formulae = reduce(reduceAnd,clause.body)
#    print "Normalized clause: ", clause
    return clause

class Clause:
    """
    The RETE-UL algorithm supports conjunctions of facts in the head of a rule
    i.e.:   H1 ^ H2 ^ ... ^ H3 :- B1 ^  ^ Bm
    The Clause definition is overridden to permit this syntax (not allowed
    in definite LP or Horn rules)
    
    In addition, since we allow (in definite Horn) entailments beyond simple facts
    we ease restrictions on the form of the head to include Clauses
    """
    def __init__(self,body,head):
        self.body = body
        self.head = head
        
    def __repr__(self):
        return "%r :- %r"%(self.head,self.body)

    def n3(self):
        return u'{ %s } => { %s }'%(self.body.n3(),self.head.n3())    

def makeRule(clause,nsMap):
    vars=set()
    for child in clause.head:
        if isinstance(child,Or):
            #Disjunction in the head, skip this rule:
            #When a disjunction occurs on the r.h.s. of a subclass axiom it 
            #becomes a disjunction in the head of the corresponding rule, and 
            #this cannot be handled within the def-Horn framework.            
            return None
        assert isinstance(child,Uniterm),repr(child)
        vars.update([term for term in child.toRDFTuple() if isinstance(term,Variable)])
    for child in clause.body:
        assert isinstance(child,Uniterm),repr(child)
        vars.update([term for term in child.toRDFTuple() if isinstance(term,Variable)])        
    return Rule(clause,declare=vars,nsMapping=nsMap)

def MapDLPtoNetwork(network,factGraph,complementExpansions=[]):
    ruleset=[]
    for horn_clause in T(factGraph,complementExpansions=complementExpansions):
#        print "## RIF BLD Horn Rules: Before LloydTopor: ##\n",horn_clause
#        print "## RIF BLD Horn Rules: After LloydTopor: ##"
        for tx_horn_clause in LloydToporTransformation(horn_clause):
            tx_horn_clause = NormalizeClause(tx_horn_clause)
#            print tx_horn_clause
            disj = [i for i in breadth_first(tx_horn_clause.body) if isinstance(i,Or)]
            import warnings
            if len(disj)>1:
                raise
                warnings.warn("No support for multiple disjunctions in the body:\n"+repr(tx_horn_clause),UserWarning,1)
            elif disj:
                #Disjunctions in the body
#                print "Disjunction in the body!"
#                print tx_horn_clause
                disj = disj[0]
                for item in disj:
#                    print "\tDisjunction operand: ", item
                    #replace disj with item in tx_horn_clause.body
                    list(breadth_first_replace(tx_horn_clause.body,candidate=disj,replacement=item))
                    #Then we want to clone the horn clause with the replacement
                    tx_clause_clone = copy.deepcopy(tx_horn_clause)
#                    print "\tClause after replacement: ", tx_clause_clone
                    for hc in ExtendN3Rules(network,NormalizeClause(tx_clause_clone)):
                        ruleset.append(makeRule(hc,network.nsMap))
                    #restore the replaced term (for the subsequent iteration)
                    list(breadth_first_replace(tx_horn_clause.body,candidate=item,replacement=disj))
            else:
#                print "No Disjunction in the body"
#                print tx_horn_clause
                for hc in ExtendN3Rules(network,NormalizeClause(tx_horn_clause)):
                    _rule=makeRule(hc,network.nsMap)
                    if _rule is not None:
                        ruleset.append(_rule)                    
            #Extract free variables anre add rule to ruleset
#        print "#######################"
    print "########## Finished Building decision network from DLP ##########"
    #renderNetwork(network).write_graphviz('out.dot')
    return ruleset

def IsaFactFormingConclusion(head):
    """
    'Relative to the def-Horn ruleset, the def-LP is thus sound; moreover, it is 
    complete for fact-form conclusions, i.e., for queries whose answers amount 
    to conjunctions of facts. However, the def-LP is a mildly weaker version of 
    the def-Horn ruleset, in the following sense. Every conclusion of the def-LP
    must have the form of a fact. By contrast, the entailments, i.e., conclusions, 
    of the def-Horn ruleset are not restricted to be facts.' - Scan depth-first
    looking for Clauses
    """
    if isinstance(head,And):
        for i in head:
            if not IsaFactFormingConclusion(i):
                return False
        return True
    elif isinstance(head,Or):
        return False
    elif isinstance(head,Atomic):
        return True
    elif isinstance(head,Clause):
        return False
    else:
        print head
        raise

def traverseClause(condition):
    if isinstance(condition,SetOperator):
        for i in iter(condition):
            yield i
    elif isinstance(condition,Atomic):
        return 

def breadth_first(condition,children=traverseClause):
    """Traverse the nodes of a tree in breadth-first order.
    The first argument should be the tree root; children
    should be a function taking as argument a tree node and
    returning an iterator of the node's children.
    
    From http://ndirty.cute.fi/~karttu/matikka/Python/eppsteins_bf_traversal_231503.htm
    
    """
    yield condition
    last = condition
    for node in breadth_first(condition,children):
        for child in children(node):
            yield child
            last = child
        if last == node:
            return

def breadth_first_replace(condition,
                          children=traverseClause,
                          candidate=None,
                          replacement=None):
    """Traverse the nodes of a tree in breadth-first order.
    The first argument should be the tree root; children
    should be a function taking as argument a tree node and
    returning an iterator of the node's children.
    
    From http://ndirty.cute.fi/~karttu/matikka/Python/eppsteins_bf_traversal_231503.htm
    
    """
    yield condition
    last = condition
    for node in breadth_first_replace(condition,
                                      children,
                                      candidate,
                                      replacement):
        for child in children(node):
            yield child
            if candidate and child is candidate:
                #replace candidate with replacement
                i=node.formulae.index(child)
                node.formulae[i]=replacement
                return
            last = child
        if last == node:
            return

def ExtendN3Rules(network,horn_clause):
    """
    Extends the network with the given Horn clause (rule)
    """
    rt=[]
    ruleStore = network.ruleStore
    lhs = BNode()
    rhs = BNode()
    assert isinstance(horn_clause.body,(And,Uniterm)),list(horn_clause.body)
    assert len(list(horn_clause.body))
#    print horn_clause
    for term in horn_clause.body:
        ruleStore.formulae.setdefault(lhs,Formula(lhs)).append(term.toRDFTuple())
    assert isinstance(horn_clause.head,(And,Uniterm))
#    if isinstance(horn_clause.head,And):
#        horn_clause.head = And([generatorFlattener(innerFunc(owlGraph,c,variable)) 
#                   for c in conjuncts])
    #print horn_clause
    if IsaFactFormingConclusion(horn_clause.head):
        def extractBNodes(term):
            if isinstance(term,BNode):
                yield term
            elif isinstance(term,Uniterm):
                for t in term.toRDFTuple():
                    if isinstance(t,BNode):
                        yield t
        exist=[list(extractBNodes(i)) for i in breadth_first(horn_clause.head)]
        e=Exists(formula=horn_clause.head,
                 declare=set(reduce(lambda x,y:x+y,exist,[])))        
        if reduce(lambda x,y:x+y,exist):
            horn_clause.head=e
            assert e.declare,exist
        for term in horn_clause.head:
            assert not hasattr(term,'next')
            if isinstance(term,Or):
                ruleStore.formulae.setdefault(rhs,Formula(rhs)).append(term)
            else:
                ruleStore.formulae.setdefault(rhs,Formula(rhs)).append(term.toRDFTuple())
        ruleStore.rules.append((ruleStore.formulae[lhs],ruleStore.formulae[rhs]))
        network.buildNetwork(iter(ruleStore.formulae[lhs]),
                             iter(ruleStore.formulae[rhs]),
                             horn_clause)
        network.alphaNodes = [node for node in network.nodes.values() if isinstance(node,AlphaNode)]
        rt.append(horn_clause)
    else:
        for hC in LloydToporTransformation(horn_clause,fullReduction=True):
            rt.append(hC)
            #print "normalized clause: ", hC
            for i in ExtendN3Rules(network,hC):
                rt.append(hC)
    return rt

def generatorFlattener(gen):
    assert hasattr(gen,'next')
    i = list(gen)
    i = len(i)>1 and [hasattr(i2,'next') and generatorFlattener(i2) or i2 for i2 in i] or i[0]
    if hasattr(i,'next'):
        i=listOrThingGenerator(i)
        #print i
        return i
    elif isinstance(i,SetOperator):
        i.formulae = [hasattr(i2,'next') and generatorFlattener(i2) or i2 for i2 in i.formulae]
        #print i
        return i
    else:
        return i

def T(owlGraph,complementExpansions=[]):
    """
    #Subsumption (purely for TBOX classification)
    {?C rdfs:subClassOf ?SC. ?A rdfs:subClassOf ?C} => {?A rdfs:subClassOf ?SC}.
    {?C owl:equivalentClass ?A} => {?C rdfs:subClassOf ?A. ?A rdfs:subClassOf ?C}.
    {?C rdfs:subClassOf ?SC. ?SC rdfs:subClassOf ?C} => {?C owl:equivalentClass ?SC}.
    
    T(rdfs:subClassOf(C,D))       -> Th(D(y)) :- Tb(C(y))
    
    T(owl:equivalentClass(C,D)) -> { T(rdfs:subClassOf(C,D) 
                                     T(rdfs:subClassOf(D,C) }
    
    A generator over the Logic Programming rules which correspond
    to the DL  ( unary predicate logic ) subsumption axiom described via rdfs:subClassOf
    """
    for c,p,d in owlGraph.triples((None,RDFS.subClassOf,None)):
        yield NormalizeClause(Clause(Tb(owlGraph,c),Th(owlGraph,d)))
        assert isinstance(c,URIRef) 
    for c,p,d in owlGraph.triples((None,OWL_NS.equivalentClass,None)):
        yield NormalizeClause(Clause(Tb(owlGraph,c),Th(owlGraph,d)))
        yield NormalizeClause(Clause(Tb(owlGraph,d),Th(owlGraph,c)))
    for s,p,o in owlGraph.triples((None,OWL_NS.intersectionOf,None)):
        if s not in complementExpansions:
            conjunction=[]
            for bodyTerm in Collection(owlGraph,o):
                bodyUniTerm = Uniterm(RDF.type,[Variable("X"),bodyTerm],
                                      newNss=owlGraph.namespaces())                                    
                classifyingClause = NormalizeClause(Clause(Tb(owlGraph,bodyTerm),
                                                 bodyUniTerm))
                if isinstance(bodyTerm,URIRef):
                    conjunction.append(bodyUniTerm)
                elif (bodyTerm,OWL_NS.someValuesFrom,None) in owlGraph or\
                     (bodyTerm,OWL_NS.hasValue,None) in owlGraph:                    
                    conjunction.extend(NormalizeClause(Clause(Tb(owlGraph,bodyTerm),None)).body)
                elif (bodyTerm,OWL_NS.allValuesFrom,None) in owlGraph:
                    conjunction.append(bodyUniTerm)                    
                    yield classifyingClause
                elif (bodyTerm,OWL_NS.hasValue,None) in owlGraph:
                    conjunction.extend(NormalizeClause(Clause(Tb(owlGraph,bodyTerm),None)).body)
                elif (bodyTerm,OWL_NS.unionOf,None) in owlGraph:
                    conjunction.append(bodyUniTerm)                    
                    yield classifyingClause
            body = And(conjunction)
            head = Uniterm(RDF.type,[Variable("X"),s],newNss=owlGraph.namespaces())
#            O1 ^ O2 ^ ... ^ On => S(?X)            
            yield Clause(body,head)
            if isinstance(s,URIRef):
#                S(?X) => O1 ^ O2 ^ ... ^ On                
    #            special case, owl:intersectionOf is a neccessary and sufficient
    #            criteria and should thus work in *both* directions 
    #            This rule is not added for anonymous classes
                yield Clause(head,body)
        
    for s,p,o in owlGraph.triples((None,OWL_NS.unionOf,None)):
        if isinstance(s,URIRef):
            #special case, owl:unionOf is a neccessary and sufficient
            #criteria and should thus work in *both* directions
            body = Or([Uniterm(RDF.type,[Variable("X"),i],newNss=owlGraph.namespaces()) \
                           for i in Collection(owlGraph,o)])
            head = Uniterm(RDF.type,[Variable("X"),s],newNss=owlGraph.namespaces())
            yield Clause(body,head)
    for s,p,o in owlGraph.triples((None,OWL_NS.inverseOf,None)):
        #    T(owl:inverseOf(P,Q))          -> { Q(x,y) :- P(y,x)
        #                                        P(y,x) :- Q(x,y) }
        newVar = Variable(BNode())
        body1 = Uniterm(s,[newVar,Variable("X")],newNss=owlGraph.namespaces())
        head1 = Uniterm(o,[Variable("X"),newVar],newNss=owlGraph.namespaces())
        yield Clause(body1,head1)
        newVar = Variable(BNode())
        body2 = Uniterm(o,[Variable("X"),newVar],newNss=owlGraph.namespaces())
        head2 = Uniterm(s,[newVar,Variable("X")],newNss=owlGraph.namespaces())
        yield Clause(body2,head2)
    for s,p,o in owlGraph.triples((None,RDF.type,OWL_NS.TransitiveProperty)):
        #T(owl:TransitiveProperty(P))   -> P(x,z) :- P(x,y) ^ P(y,z)
        y = Variable(BNode())
        z = Variable(BNode())
        x = Variable("X")
        body = And([Uniterm(s,[x,y],newNss=owlGraph.namespaces()),\
                    Uniterm(s,[y,z],newNss=owlGraph.namespaces())])
        head = Uniterm(s,[x,z],newNss=owlGraph.namespaces())
        yield Clause(body,head)
    for s,p,o in owlGraph.triples_choices((None,
                                           [RDFS.range,RDFS.domain],
                                           None)):
        if p == RDFS.range:
            #T(rdfs:range(P,D))  -> D(y) := P(x,y)        
            x = Variable("X")
            y = Variable(BNode())
            body = Uniterm(s,[x,y],newNss=owlGraph.namespaces())
            head = Uniterm(RDF.type,[y,o],newNss=owlGraph.namespaces())
            yield Clause(body,head)
        else: 
            #T(rdfs:domain(P,D)) -> D(x) := P(x,y)
            x = Variable("X")
            y = Variable(BNode())
            body = Uniterm(s,[x,y],newNss=owlGraph.namespaces())
            head = Uniterm(RDF.type,[x,o],newNss=owlGraph.namespaces())
            yield Clause(body,head)
            
def LloydToporTransformation(clause,fullReduction=False):
    """
    Tautological, common horn logic forms (useful for normalizing 
    conjunctive & disjunctive clauses)
    
    (H ^ H0) :- B                 -> { H  :- B
                                       H0 :- B }
    (H :- H0) :- B                -> H :- B ^ H0
    
    H :- (B v B0)                 -> { H :- B
                                       H :- B0 }
    """
    assert isinstance(clause,Clause),repr(clause)
    if isinstance(clause.body,Or):
        for atom in clause.body.formulae:
            yield Clause(atom,clause.head)
    elif isinstance(clause.head,Clause):
        yield Clause(And([clause.body,clause.head.body]),clause.head.head)
    elif isinstance(clause.head,Or):
        #Disjunction in the body, not supported by def-Horn
        #skip
        return
    elif not isinstance(clause.body,Condition):
        print clause.head
        raise
    elif fullReduction and isinstance(clause.head,And):
        for i in clause.head:
            for j in LloydToporTransformation(Clause(clause.body,i),
                                              fullReduction=fullReduction):
                if [i for i in breadth_first(j.head) if isinstance(i,And)]:
                    #Ands in the head need to be further flattened
                    yield NormalizeClause(j) 
                else:
                    yield j
    else:
        yield clause
    

def commonConjunctionMapping(owlGraph,conjuncts,innerFunc,variable=Variable("X")):
    """
    DHL: T*((C1 ^ C2 ^ ... ^ Cn),x)    -> T*(C1,x) ^ T*(C2,x) ^ ... ^ T*(Cn,x)
    OWL: intersectionOf(c1 ÔøΩ c2 ,..,cn) =>  EC(c1) ‚à© ‚Ä¶ ‚à© EC(cn)
    """
    conjuncts = Collection(owlGraph,conjuncts)
    return And([generatorFlattener(innerFunc(owlGraph,c,variable)) 
                   for c in conjuncts])

def Th(owlGraph,_class,variable=Variable('X'),position=LHS):
    """
    DLP head (antecedent) knowledge assertional forms (ABox assertions, conjunction of
    ABox assertions, and universal role restriction assertions)
    Th(A,x)                      -> A(x)
    Th((C1 ^ C2 ^ ... ^ Cn),x)   -> Th(C1,x) ^ Th(C2,x) ^ ... ^ Th(Cn,x) 
    Th((‚àÄR.C),x)                -> Th(C(y)) :- R(x,y)
    """
    props = list(set(owlGraph.predicates(subject=_class)))
    if OWL_NS.allValuesFrom in props:
        #http://www.w3.org/TR/owl-semantics/#owl_allValuesFrom
        #restriction(p allValuesFrom(r))    {x ‚àà O | <x,y> ‚àà ER(p) implies y ‚àà EC(r)}
        for s,p,o in owlGraph.triples((_class,OWL_NS.allValuesFrom,None)):
            prop = list(owlGraph.objects(subject=_class,predicate=OWL_NS.onProperty))[0]
            newVar = Variable(BNode())
            body = Uniterm(prop,[variable,newVar],newNss=owlGraph.namespaces())
            for head in Th(owlGraph,o,variable=newVar):
                yield Clause(body,head)
    elif OWL_NS.someValuesFrom in props:
        #http://www.w3.org/TR/owl-semantics/#someValuesFrom
        #estriction(p someValuesFrom(e)) {x ‚àà O | ‚àÉ <x,y> ‚àà ER(p) ‚àß y ‚àà EC(e)}
        for s,p,o in owlGraph.triples((_class,OWL_NS.someValuesFrom,None)):
            prop = list(owlGraph.objects(subject=_class,predicate=OWL_NS.onProperty))[0]
            newVar = BNode()
            yield And([Uniterm(prop,[variable,newVar],newNss=owlGraph.namespaces()),
                        generatorFlattener(Th(owlGraph,o,variable=newVar))])
    else:
        #Simple class
        yield Uniterm(RDF.type,[variable,_class],newNss=owlGraph.namespaces())
    
def Tb(owlGraph,_class,variable=Variable('X')):
    """
    DLP body (consequent knowledge assertional forms (ABox assertions, 
    conjunction / disjunction of ABox assertions, and exisential role restriction assertions)
    These are all common EL++ templates for KR
    Tb(A(x))                      -> A(x)
    Tb((C1 ^ C2 ^ ... ^ Cn),x)    -> Tb(C1,x) ^ Tb(C2,x) ^ ... ^ Tb(Cn,x)
    Tb((C1 v C2 v ... v Cn),x)    -> Tb(C1,x) v Tb(C2,x) v ... v Tb(Cn,x)
    Tb((‚àÉR.C),x)                 ->  R(x,y) ^ Tb(C,y) 
    """
    props = list(set(owlGraph.predicates(subject=_class)))
    if OWL_NS.unionOf in props and not isinstance(_class,URIRef):
        #http://www.w3.org/TR/owl-semantics/#owl_unionOf
        #OWL semantics: unionOf(c1 ‚Ä¶ cn) => EC(c1) ‚à™ ‚Ä¶ ‚à™ EC(cn)
        for s,p,o in owlGraph.triples((_class,OWL_NS.unionOf,None)):
            yield Or([Tb(owlGraph,c,variable=variable) \
                           for c in Collection(owlGraph,o)])
    elif OWL_NS.someValuesFrom in props:
        #http://www.w3.org/TR/owl-semantics/#owl_someValuesFrom
        #estriction(p someValuesFrom(e)) {x ‚àà O | ‚àÉ <x,y> ‚àà ER(p) ‚àß y ‚àà EC(e)}
        prop = list(owlGraph.objects(subject=_class,predicate=OWL_NS.onProperty))[0]
        o =list(owlGraph.objects(subject=_class,predicate=OWL_NS.someValuesFrom))[0]
        newVar = Variable(BNode())
        body = Uniterm(prop,[variable,newVar],newNss=owlGraph.namespaces())
        head = Th(owlGraph,o,variable=newVar)
        yield And([Uniterm(prop,[variable,newVar],newNss=owlGraph.namespaces()),
                    generatorFlattener(Tb(owlGraph,o,variable=newVar))])
    elif OWL_NS.hasValue in props:
        #http://www.w3.org/TR/owl-semantics/#owl_hasValue
        #Domain-specific rules for hasValue
        #Can be achieved via pD semantics        
        prop = list(owlGraph.objects(subject=_class,predicate=OWL_NS.onProperty))[0]
        o =first(owlGraph.objects(subject=_class,predicate=OWL_NS.hasValue))
        yield Uniterm(prop,[variable,o],newNss=owlGraph.namespaces())
    else:
        #simple class
        #"Named" Uniterm
        yield Uniterm(RDF.type,[variable,_class],newNss=owlGraph.namespaces())