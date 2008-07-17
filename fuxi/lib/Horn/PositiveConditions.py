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

def buildUniTerm((s,p,o),newNss=None):
    return Uniterm(p,[s,o],newNss=newNss)

class QNameManager:
    def __init__(self,nsDict=None):
        self.nsDict = nsDict and nsDict or {}
        self.nsMgr = NamespaceManager(Graph())
        self.nsMgr.bind('owl','http://www.w3.org/2002/07/owl#')
        self.nsMgr.bind('math','http://www.w3.org/2000/10/swap/math#')
        
    def bind(self,prefix,namespace):
        self.nsMgr.bind(prefix,namespace)

class SetOperator:
    def repr(self,operator):
        return "%s( %s )"%(operator,' '.join([repr(i) for i in self.formulae]))
    def __len__(self):
        return len(self.formulae)

class Condition:
    """
    CONDITION   ::= CONJUNCTION | DISJUNCTION | EXISTENTIAL | ATOMIC
    """
    def __iter__(self):
        for f in self.formulae:
            yield f

class And(QNameManager,SetOperator,Condition):
    """
    CONJUNCTION ::= 'And' '(' CONDITION* ')'
    
    >>> And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    And( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) )
    """
    def __init__(self,formulae=None):
        self.formulae = formulae and formulae or []
        QNameManager.__init__(self)
        
    def n3(self):
        """
        >>> And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
        ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])]).n3()
        u'rdfs:comment a rdf:Property .\\n owl:Class a rdfs:Class'
        
        """
#        if not [term for term in self if not isinstance(term,Uniterm)]:
#            g= Graph(namespace_manager = self.nsMgr)
#            g.namespace_manager= self.nsMgr
#            [g.add(term.toRDFTuple()) for term in self]
#            return g.serialize(format='n3')
#        else:
        return u' .\n '.join([i.n3() for i in self])
        
    def __repr__(self):
        return self.repr('And')
    
class Or(QNameManager,SetOperator,Condition):
    """
    DISJUNCTION ::= 'Or' '(' CONDITION* ')'
    
    >>> Or([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    Or( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) )
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
    Exists ?X ?Y ( Or( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) ) )
    """
    def __init__(self,formula=None,declare=None):
        self.formula = formula
        self.declare = declare and declare or []    
    def __iter__(self):
        for term in self.formula: 
            yield term
    def n3(self):
        """
        """
        return self.formula.n3()
        #return u"@forSome %s %s"%(','.join(self.declare),self.formula.n3())
    
    def __repr__(self):
        return "Exists %s ( %r )"%(' '.join([var.n3() for var in self.declare]),
                                   self.formula )
        
class Atomic(Condition):
    """
    ATOMIC ::= Uniterm | Equal | Member | Subclass (| Frame)
    """
    def __iter__(self):
        yield self

class Equal(QNameManager,Atomic):
    """
    Equal ::= TERM '=' TERM
    TERM ::= Const | Var | Uniterm | 'External' '(' Expr ')'
    
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
    
    We restrict to binary predicates (RDF triples)
    
    >>> Uniterm(RDF.type,[RDFS.comment,RDF.Property])
    rdf:Property(rdfs:comment)
    """
    def __init__(self,op,arg=None,newNss=None):        
        self.op = op
        self.arg = arg and arg or []
        QNameManager.__init__(self)
        if newNss is not None:
            newNss = isinstance(newNss,dict) and newNss.items() or newNss
            for k,v in newNss:
                self.nsMgr.bind(k,v)
        
    def renderTermAsN3(self,term):
        if term == RDF.type:
            return 'a'
        elif isinstance(term, (BNode,Literal,Variable)):
            return term.n3()
        else:
            return self.nsMgr.qname(term)
        
    def n3(self):
        """
        Serialize as N3 (using available namespace managers)
        
        >>> Uniterm(RDF.type,[RDFS.comment,RDF.Property]).n3()
        u'rdfs:comment a rdf:Property'

        """
        return ' '.join([ self.renderTermAsN3(term) 
                         for term in [self.arg[0],self.op,self.arg[1]]])
        
    def toRDFTuple(self):
        subject,_object = self.arg
        return (subject,self.op,_object)
        
    def collapseName(self,val):
        try:
            return self.nsMgr.qname(val)
        except:
            return val
        
    def __repr__(self):
        arg0,arg1 = self.arg
        pred = isinstance(self.op,Variable) and self.op.n3() or \
               self.collapseName(self.op)
        subj = isinstance(arg0,(Variable,BNode)) and arg0.n3() or \
               self.collapseName(arg0)
        obj  = isinstance(arg1,(Variable,BNode)) and arg1.n3() or \
               self.collapseName(arg1)    
        if self.op == RDF.type:
            return "%s(%s)"%(obj,subj)
        else:
            return "%s(%s %s)"%(pred,
                                subj,
                                obj)
            
class ExternalFunction(Uniterm):
    """
    An External(ATOMIC) is a call to an externally defined predicate, equality, 
    membership, subclassing, or frame. Likewise, External(Expr) is a call to an 
    externally defined function.
    >>> ExternalFunction(Uniterm(URIRef('http://www.w3.org/2000/10/swap/math#greaterThan'),[Variable('VAL'),Literal(2)]))
    math:greaterThan(?VAL 2)
    """
    def __init__(self,builtin,newNss=None):
        from FuXi.Rete.RuleStore import N3RuleStore,N3Builtin
        self.builtin= builtin
        if isinstance(builtin,N3Builtin):
            Uniterm.__init__(self,builtin.uri,[builtin.argument,builtin.result])
        else:
            Uniterm.__init__(self,builtin.op,builtin.arg)
        QNameManager.__init__(self)
        if newNss is not None:
            newNss = isinstance(newNss,dict) and newNss.items() or newNss
            for k,v in newNss:
                self.nsMgr.bind(k,v)
            
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()