#!/usr/local/bin/python
# -*- coding: utf-8 -*-
"""
The language of positive RIF conditions determines what can appear as a body (the
 if-part) of a rule supported by the basic RIF logic. As explained in Section 
 Overview, RIF's Basic Logic Dialect corresponds to definite Horn rules, and the
  bodies of such rules are conjunctions of atomic formulas without negation.
"""
from rdflib import Variable, BNode, URIRef, Literal, Namespace,RDF,RDFS
from rdflib.Collection import Collection
from rdflib.Graph import ConjunctiveGraph,QuotedGraph,ReadOnlyGraphAggregate, Graph
from rdflib.syntax.NamespaceManager import NamespaceManager

OWL    = Namespace("http://www.w3.org/2002/07/owl#")

class QNameManager:
    def __init__(self,nsDict=None):
        self.nsDict = nsDict and nsDict or {}
        self.nsMgr = NamespaceManager(Graph())
        self.nsMgr.bind('owl','http://www.w3.org/2002/07/owl#')
        
    def bind(self,prefix,namespace):
        self.nsMgr.bind(prefix,namespace)

class _SetOperatorSerializer:
    def repr(self,operator):
        return "%s(%s)"%(operator,' '.join([repr(i) for i in self.formulae]))
    

class Condition:
    """
    CONDITION   ::= CONJUNCTION | DISJUNCTION | EXISTENTIAL | ATOMIC
    """
    pass

class And(QNameManager,_SetOperatorSerializer,Condition):
    """
    CONJUNCTION ::= 'And' '(' CONDITION* ')'
    
    >>> And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    And(rdf:Property(rdfs:comment) rdfs:Class(owl:Class))
    """
    def __init__(self,formulae=None):
        self.formulae = formulae and formulae or []
        QNameManager.__init__(self)
        
    def __repr__(self):
        return self.repr('And')
    
class Or(QNameManager,_SetOperatorSerializer,Condition):
    """
    DISJUNCTION ::= 'Or' '(' CONDITION* ')'
    
    >>> Or([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    Or(rdf:Property(rdfs:comment) rdfs:Class(owl:Class))
    """
    def __init__(self,formulae=None):
        self.formulae = formulae and formulae or []
        QNameManager.__init__(self)
        
    def __repr__(self):
        return self.repr('Or')

class Exists(Condition):
    """
    EXISTENTIAL ::= 'Exists' Var+ '(' CONDITION ')'
    >>> Exists(formula=Or([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...                    Uniterm(RDF.type,[OWL.Class,RDFS.Class])]),
    ...        declare=[Variable('X'),Variable('Y')])
    Exists ?X ?Y ( Or(rdf:Property(rdfs:comment) rdfs:Class(owl:Class)) )
    """
    def __init__(self,formula=None,declare=None):
        self.formula = formula
        self.declare = declare and declare or []    
    def __repr__(self):
        return "Exists %s ( %r )"%(' '.join([var.n3() for var in self.declare]),
                                   self.formula )

class Atomic(Condition):
    """
    ATOMIC ::= Uniterm | Equal
    """
    pass

class Equal(QNameManager,Atomic):
    """
    Equal ::= TERM '=' TERM
    TERM ::= Const | Var | Uniterm
    
    >>> Equal(RDFS.Resource,OWL.Thing)
    rdfs:Resource =  owl:Thing
    """
    def __init__(self,lhs=None,rhs=None):
        self.lhs = lhs
        self.rhs = rhs
        QNameManager.__init__(self)
        
    def __repr__(self):
        left  = self.nsMgr.qname(self.lhs)
        right = self.nsMgr.qname(self.rhs)
        return "%s =  %s"%(left,right)

class Uniterm(QNameManager,Atomic):
    """
    Uniterm ::= Const '(' TERM* ')'
    TERM ::= Const | Var | Uniterm
    
    We restrict to binary predicates
    
    >>> Uniterm(RDF.type,[RDFS.comment,RDF.Property])
    rdf:Property(rdfs:comment)
    """
    def __init__(self,op,arg=None):        
        self.op = op
        self.arg = arg and arg or []
        QNameManager.__init__(self)
        
    def __repr__(self):
        arg0,arg1 = self.arg
        pred = isinstance(self.op,Variable) and self.op.n3() or \
               self.nsMgr.qname(self.op)
        subj = isinstance(arg0,Variable) and arg0.n3() or \
               self.nsMgr.qname(arg0)
        obj  = isinstance(arg1,Variable) and arg1.n3() or \
               self.nsMgr.qname(arg1)
        if self.op is RDF.type:
            return "%s(%s)"%(obj,subj)
        else:
            return "%s(%s,%s)"%(pred,
                                subj,
                                obj)

def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()