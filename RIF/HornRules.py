#!/usr/local/bin/python
# -*- coding: utf-8 -*-
"""
This section defines Horn rules for RIF Phase 1. The syntax and semantics 
incorporates RIF Positive Conditions defined in Section Positive Conditions
"""
from PositiveConditions import *
from rdflib import Variable, BNode, URIRef, Literal, Namespace,RDF,RDFS

class Ruleset:
    """
    Ruleset ::= RULE*
    """
    def __init__(self,formulae=None):
        self.formulae = formulae and formulae or []

class Rule:
    """
    RULE ::= 'Forall' Var* CLAUSE
    
    Example: {?C rdfs:subClassOf ?SC. ?M a ?C} => {?M a ?SC}.
    
    >>> clause = Clause(And([Uniterm(RDFS.subClassOf,[Variable('C'),Variable('SC')]),
    ...                      Uniterm(RDF.type,[Variable('M'),Variable('C')])]),
    ...                 Uniterm(RDF.type,[Variable('M'),Variable('SC')]))
    >>> Rule(clause,[Variable('M'),Variable('SC'),Variable('C')])
    Forall ?M ?SC ?C ?SC(?M) :- And(rdfs:subClassOf(?C,?SC) ?C(?M))
    
    """
    def __init__(self,clause,declare=None):
        self.formula = clause
        self.declare = declare and declare or []

    def __repr__(self):
        return "Forall %s %r"%(' '.join([var.n3() for var in self.declare]),
                               self.formula)
    
class Clause:
    """
    Facts are *not* modelled formally as rules with empty bodies
    
    Implies ::= ATOMIC ':-' CONDITION
    
    Use body / head instead of if/then (native language clash)
    
    Example: {?C rdfs:subClassOf ?SC. ?M a ?C} => {?M a ?SC}.
    
    >>> Clause(And([Uniterm(RDFS.subClassOf,[Variable('C'),Variable('SC')]),
    ...             Uniterm(RDF.type,[Variable('M'),Variable('C')])]),
    ...        Uniterm(RDF.type,[Variable('M'),Variable('SC')]))
    ?SC(?M) :- And(rdfs:subClassOf(?C,?SC) ?C(?M))
    """
    def __init__(self,body,head):
        self.body = body
        self.head = head
        assert isinstance(head,Atomic)
        assert isinstance(body,Condition)
        
    def __repr__(self):
        return "%r :- %r"%(self.head,self.body)
        
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()