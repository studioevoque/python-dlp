#!/usr/bin/env python
# encoding: utf-8
"""
Implementation of Sideways Information Passing graph (builds it from a given ruleset)
"""

import unittest, os, sys, itertools
from FuXi.Horn.PositiveConditions import *
from FuXi.Horn.HornRules import Ruleset
from FuXi.Rete.RuleStore import SetupRuleStore, N3Builtin
from FuXi.DLP import SKOLEMIZED_CLASS_NS
from rdflib.util import first
from rdflib.Graph import Graph
from rdflib.Collection import Collection
from testMagic import *
from cStringIO import StringIO
from pprint import pprint;
from rdflib import Namespace

MAGIC = Namespace('http://doi.acm.org/10.1145/28659.28689#')

def iterCondition(condition):
    return isinstance(condition,SetOperator) and condition or iter([condition])

class SIPGraphArc(object):
    """
    A sip for r is a labeled graph that satisfies the following conditions:
    1. Each node is either a subset or a member of P(r) or {ph}.
    2. Each arc is of the form N -> q, with label X, where N is a subset of P (r) or {ph}, q is a
    member of P(r), and X is a set of variables, such that
    (i) Each variable of X appears in N.
    (ii) Each member of N is connected to a variable in X.
    (iii) For some argument of q, all its variables appear in X. Further, each variable of X
    appears in an argument of q that satisfies this condition.    
    """
    def __init__(self, left, right, variables, graph=None, headPassing = False):
        self.variables=variables
        self.left = left
        self.right = right
        self.graph = graph is None and Graph() or graph
        self.arc = SKOLEMIZED_CLASS_NS[BNode()]
        self.graph.add((self.arc,RDF.type,MAGIC.SipArc))
        varsCol = Collection(self.graph,BNode())
        [ varsCol.append(i) for i in self.variables ]
        self.graph.add((self.arc,MAGIC.bindings,varsCol.uri))
        if headPassing:
            self.boundHeadPredicate = True
            self.graph.add((self.left,self.arc,self.right))
        else:
            self.boundHeadPredicate = False
            self.graph.add((self.left,self.arc,self.right))
    def __repr__(self):
        """Visual of graph arc"""
        return "%s - (%s) > %s"%(self.left,self.variables,self.right)        
        
def CollectSIPArcVars(left,right):
    """docstring for CollectSIPArcVars"""
    if isinstance(left,list):
        return set(reduce(lambda x,y:x+y,
                          [GetArgs(t) for t in left])).intersection(GetArgs(right))
    else:
        return set(GetArgs(left)).intersection(GetArgs(right))
        
def GetOp(term):
    if isinstance(term,N3Builtin):
        return term.uri
    elif isinstance(term,Uniterm):
        return term.op == RDF.type and term.arg[-1] or term.op
    else:
        print term
        raise term        
        
def GetArgs(term):
    if isinstance(term,N3Builtin):
        return term.argument
    elif isinstance(term,Uniterm):
        return term.arg
    else:
        raise term        
        
def IncomingSIPArcs(sip,pred):
    """docstring for IncomingSIPArcs"""
    for s,p,o in [(s1,p1,o1) for (s1,p1,o1) in sip.triples((None,None,pred)) 
        if (p1,RDF.type,MAGIC.SipArc) in sip]:
        yield Collection(sip,s),Collection(sip,first(sip.objects(p,MAGIC.bindings)))
        
def validSip(sipGraph):
    if not len(sipGraph): return False
    for bindingCol in sipGraph.query("SELECT ?arc { [ a m:BoundHeadPredicate; ?arc ?pred ]. ?arc m:bindings [ rdf:first ?val ] }",
                                     initNs={'m':MAGIC}):
        return True
    return False
        
def BuildNaturalSIP(clause,derivedPreds=None):
    """
    Natural SIP:
    
    Informally, for a rule of a program, a sip represents a
    decision about the order in which the predicates of the rule will be evaluated, and how values
    for variables are passed from predicates to other predicates during evaluation
    
    >>> ruleStore,ruleGraph=SetupRuleStore(StringIO(PROGRAM2))
    >>> ruleStore._finalize()
    >>> fg=Graph().parse(StringIO(PROGRAM2),format='n3')
    >>> rs=Ruleset(n3Rules=ruleGraph.store.rules,nsMapping=ruleGraph.store.nsMgr)
    >>> for rule in rs: print rule
    Forall ?Y ?X ( ex:sg(?X ?Y) :- ex:flat(?X ?Y) )
    Forall ?Y ?Z4 ?X ?Z1 ?Z2 ?Z3 ( ex:sg(?X ?Y) :- And( ex:up(?X ?Z1) ex:sg(?Z1 ?Z2) ex:flat(?Z2 ?Z3) ex:sg(?Z3 ?Z4) ex:down(?Z4 ?Y) ) )
    >>> sip=BuildNaturalSIP(list(rs)[-1])
    >>> for N,x in IncomingSIPArcs(sip,MAGIC.sg): print N.n3(),x.n3()
    ( <http://doi.acm.org/10.1145/28659.28689#up> <http://doi.acm.org/10.1145/28659.28689#sg> <http://doi.acm.org/10.1145/28659.28689#flat> ) ( ?Z3 )
    ( <http://doi.acm.org/10.1145/28659.28689#up> <http://doi.acm.org/10.1145/28659.28689#sg> ) ( ?Z1 )
    
    >>> sip=BuildNaturalSIP(list(rs)[-1],[MAGIC.sg])
    >>> list(sip.query('SELECT ?q {  ?prop a magic:SipArc . [] ?prop ?q . }',initNs={u'magic':MAGIC}))
    [rdflib.URIRef('http://doi.acm.org/10.1145/28659.28689#sg'), rdflib.URIRef('http://doi.acm.org/10.1145/28659.28689#sg')]
    """
    from FuXi.Rete.Util import permu
    assert isinstance(clause.head,Uniterm),"Only one literal in the head!"
    def collectSip(left,right):
        if isinstance(left,list):
            vars=CollectSIPArcVars(left,right)
            leftList=Collection(sipGraph,None)
            assert len(left)==len(set(left))            
            [leftList.append(i) for i in [GetOp(ii) for ii in left]]
            left.append(right)                        
            arc=SIPGraphArc (leftList.uri,GetOp(right),vars,sipGraph)
            return left
        else:
            vars=CollectSIPArcVars(left,right)
            ph=GetOp(left)
            q=GetOp(right)
            arc=SIPGraphArc(ph,q,vars,sipGraph,headPassing=True)
            sipGraph.add((ph,RDF.type,MAGIC.BoundHeadPredicate))
            rt=[left,right]
        return rt
    sipGraph=Graph()  
    if isinstance(clause.body,And):
        foundSipOrder = False
        bodyOrders = permu(clause.body.formulae)
        while not foundSipOrder:
            try:
                bodyOrder=bodyOrders.next()
                reduce(collectSip,
                       itertools.chain(
                              iterCondition(clause.head),
                              iterCondition(And(bodyOrder))))        
                if not validSip(sipGraph):
                    sipGraph.remove((None,None,None))
                else:
                    foundSipOrder=True
                    sipGraph.sipOrder = And(bodyOrder)
            except StopIteration:
                raise Exception("Couldn't find a valid SIP for %s"%clause)
    else:
        reduce(collectSip,itertools.chain(iterCondition(clause.head),
                                          iterCondition(clause.body)))
        sipGraph.sipOrder = clause.body        
    if derivedPreds:
        # We therefore generalize our notation to allow
        # more succint representation of sips, in which only arcs entering 
        # derived predicates are represented.
        arcsToRemove=[]
        collectionsToClear=[]
        for N,prop,q in sipGraph.query(
            'SELECT ?N ?prop ?q {  ?prop a magic:SipArc . ?N ?prop ?q . }',
            initNs={u'magic':MAGIC}):
            if q not in derivedPreds:
                arcsToRemove.extend([(N,prop,q),(prop,None,None)])
                collectionsToClear.append(Collection(sipGraph,N))
                #clear bindings collection as well
                bindingsColBNode=first(sipGraph.objects(prop,MAGIC.bindings))
                collectionsToClear.append(Collection(sipGraph,bindingsColBNode))
        for removeSts in arcsToRemove:
            sipGraph.remove(removeSts)
        for col in collectionsToClear:
            col.clear()
    return sipGraph

def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()