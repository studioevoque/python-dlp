#!/usr/local/bin/python
# -*- coding: utf-8 -*-
"""
This section defines Horn rules for RIF Phase 1. The syntax and semantics 
incorporates RIF Positive Conditions defined in Section Positive Conditions
"""
from PositiveConditions import *
from rdflib import Variable, BNode, URIRef, Literal, Namespace,RDF,RDFS
from FuXi.Rete.RuleStore import N3Builtin
def ExtractVariables(clause):
    pass

class Ruleset:
    """
    Ruleset ::= RULE*
    """
    def __init__(self,formulae=None,n3Rules=None,nsMapping=None):
        self.nsMapping = nsMapping and nsMapping or {}        
        self.formulae = formulae and formulae or []
        if n3Rules:
            #Convert a N3 abstract model (parsed from N3) into a RIF BLD 
            for lhs,rhs in n3Rules:
                allVars = set()
                for ruleCondition in [lhs,rhs]:
                    for stmt in ruleCondition:
                        if isinstance(stmt,N3Builtin):
                            ExternalFunction(stmt,newNss=self.nsMapping)
#                            print stmt;raise
                        allVars.update([term for term in stmt if isinstance(term,Variable)])
                body = [isinstance(term,N3Builtin) and term or
                         Uniterm(list(term)[1],[list(term)[0],list(term)[-1]],
                                 newNss=nsMapping) for term in lhs]
                body = len(body) == 1 and body[0] or And(body)
                head = [Uniterm(p,[s,o],newNss=nsMapping) for s,p,o in rhs]
                head = len(head) == 1 and head[0] or And(head)
                self.formulae.append(Rule(Clause(body,head),declare=allVars))

    def __iter__(self):
        for f in self.formulae:
            yield f

class Rule:
    """
    RULE ::= 'Forall' Var* CLAUSE
    
    Example: {?C rdfs:subClassOf ?SC. ?M a ?C} => {?M a ?SC}.
    
    >>> clause = Clause(And([Uniterm(RDFS.subClassOf,[Variable('C'),Variable('SC')]),
    ...                      Uniterm(RDF.type,[Variable('M'),Variable('C')])]),
    ...                 Uniterm(RDF.type,[Variable('M'),Variable('SC')]))
    >>> Rule(clause,[Variable('M'),Variable('SC'),Variable('C')])
    Forall ?M ?SC ?C ( ?SC(?M) :- And( rdfs:subClassOf(?C ?SC) ?C(?M) ) )
    
    """
    def __init__(self,clause,declare=None,nsMapping=None):
        self.nsMapping = nsMapping and nsMapping or {}
        self.formula = clause
        self.declare = declare and declare or []

    def n3(self):
        """
        Render a rule as N3 (careful to use e:tuple (_: ?X) skolem functions for existentials in the head)

        >>> clause = Clause(And([Uniterm(RDFS.subClassOf,[Variable('C'),Variable('SC')]),
        ...                      Uniterm(RDF.type,[Variable('M'),Variable('C')])]),
        ...                 Uniterm(RDF.type,[Variable('M'),Variable('SC')]))        
        >>> Rule(clause,[Variable('M'),Variable('SC'),Variable('C')]).n3()
        u'{ ?C rdfs:subClassOf ?SC .\\n ?M a ?C } => { ?M a ?SC }'
                
        """
        return u'{ %s } => { %s }'%(self.formula.body.n3(),
                                    self.formula.head.n3())
#        "Forall %s ( %r )"%(' '.join([var.n3() for var in self.declare]),
#                               self.formula)
    def __repr__(self):
        return "Forall %s ( %r )"%(' '.join([var.n3() for var in self.declare]),
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
    ?SC(?M) :- And( rdfs:subClassOf(?C ?SC) ?C(?M) )
    """
    def __init__(self,body,head):
        self.body = body
        self.head = head
        #assert isinstance(head,Atomic),repr(head)
        assert isinstance(body,Condition)
        from FuXi.Rete.Network import HashablePatternList
        antHash=HashablePatternList([term.toRDFTuple() 
                            for term in body])
        consHash=HashablePatternList([term.toRDFTuple() 
                            for term in head])                                                                                            
        self._hash = hash(antHash) ^ hash(consHash)
        
    def __eq__(self,other):
        return hash(self)==hash(other)
        
    def __hash__(self):
        """
        >>> a=Clause(And([Uniterm(RDFS.subClassOf,[Variable('C'),Variable('SC')]),
        ...             Uniterm(RDF.type,[Variable('M'),Variable('C')])]),
        ...        Uniterm(RDF.type,[Variable('M'),Variable('SC')]))
        >>> b=Clause(And([Uniterm(RDFS.subClassOf,[Variable('C'),Variable('SC')]),
        ...             Uniterm(RDF.type,[Variable('M'),Variable('C')])]),
        ...        Uniterm(RDF.type,[Variable('M'),Variable('SC')]))
        >>> d=set()
        >>> d.add(a)
        >>> b in d
        True
        >>> hash(a) == hash(b)
        True
        
        """
        return self._hash
        
    def asTuple(self):
        return (self.body,self.head)
        
    def __repr__(self):
        return "%r :- %r"%(self.head,self.body)
    
    def n3(self):
        return u'{ %s } => { %s }'%(self.body.n3(),self.head.n3())    
        
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()