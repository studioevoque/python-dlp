#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
[[[
    One method, called magic sets,is a general algorithm for rewriting logical rules
so that they may be implemented bottom-UP (= forward chaining) in a way that
is that by working bottom-up, we can take advantage of efficient methods for doing
massive joins.
]]] -- Magic Sets and Other Strange Ways to Implement Logic Programs, F. Bancilhon,
D. Maier, Y. Sagiv and J. Ullman, Proc. 5th ACM SIGMOD-SIGACT Symposium on
Principles of Database Systems, 1986.
"""

import unittest, os, time, itertools, copy
from FuXi.Rete.RuleStore import SetupRuleStore, N3RuleStore, N3Builtin, LOG
from FuXi.Rete.AlphaNode import ReteToken
from FuXi.Horn.HornRules import Clause, Ruleset, Rule, HornFromN3
from FuXi.DLP import FUNCTIONAL_SEMANTCS, NOMINAL_SEMANTICS
from FuXi.Horn.PositiveConditions import *
from FuXi.Syntax.InfixOWL import OWL_NS
from cStringIO import StringIO
from rdflib.Graph import Graph
from rdflib import URIRef, RDF, RDFS, Namespace, Variable, Literal, URIRef
from rdflib.sparql.Algebra import RenderSPARQLAlgebra
from rdflib.sparql.bison import Parse
from rdflib.util import first
from testMagic import *
from SidewaysInformationPassing import BuildNaturalSIP, IncomingSIPArcs

EX_ULMAN = Namespace('http://doi.acm.org/10.1145/6012.15399#')
LOG_NS   = Namespace("http://www.w3.org/2000/10/swap/log#")
MAGIC = Namespace('http://doi.acm.org/10.1145/28659.28689#')

def MagicSetTransformation(factGraph,rules,GOALS,derivedPreds=None):
    """
    Takes a goal and a ruleset and returns an iterator
    over the rulest that corresponds to the magic set
    transformation:
    
    [[[
    
    ]]]
    """
    magicPredicates=set()
    if not derivedPreds:
        derivedPreds=list(DerivedPredicateIterator(factGraph,rules))
    replacement={}
#    for rule in rules:
#        if isinstance(rule.formula.head,And):
#            from FuXi.DLP import LloydToporTransformation
#            replacement.setdefault(rule,[]).extend([Rule(rule) 
#                            for rule in LloydToporTransformation(rule.formula)])
#    for initial,replacements in replacement.items():
#        rules.remove(initial)
#        rules.extend(replacements)
    rs=AdornProgram(factGraph,rules,GOALS,derivedPreds)
    newRules=[]
    for rule in rs: 
        magicPositions={}
        prevPredicates=[]
        #Generate magic rules
        for idx,pred in enumerate(iterCondition(rule.formula.body)):
            magicBody=[]
            if isinstance(pred,AdornedUniTerm):# and pred not in magicPredicates:
                # For each rule r in Pad, and for each occurrence of an adorned 
                # predicate p a in its body, we generate a magic rule defining magic_p a
                if 'b' not in pred.adornment:
                    raise                   
                prevPreds=[item for _idx,item in enumerate(rule.formula.body)
                                            if _idx < idx]             
                magicPred=pred.makeMagicPred()
                prevPredicates.append(magicPred)
                magicPositions[idx]=(magicPred,pred)
                inArcs=[(N,x) for (N,x) in IncomingSIPArcs(rule.sip,GetOp(pred))
                                    if not set(x).difference(pred.arg)]
                if len(inArcs) > 1:
                    print rule
                    print rule.sip.serialize(format='n3')
                    print pred, magicPred
                    raise NotImplementedError()
#                        labelLiterals=[]
#                        for idx,(N,x) in enumerate(inArcs):
#                            if not set(x).difference(pred.arg):
#                                ruleHead=Uniterm(pred.op+'_label_'+str(idx),[i for i in x])
#                                labelLiterals.append(ruleHead)
#                                ruleBody=And(buildMagicBody(
#                                    N,
#                                    [ rule.forumula.body],
#                                    rule.formula.head,
#                                    derivedPreds))
#                                magicRules.append(Rule(Clause(ruleBody,ruleHead)))
#                        magicRules.append(Rule(Clause(And(labelLiterals),magicPred)))
                else:
                    for idxSip,(N,x) in enumerate(inArcs):
                        ruleBody=And(buildMagicBody(
                                N,
                                prevPreds,
                                rule.formula.head,
                                derivedPreds))
                        newRules.append(Rule(Clause(ruleBody,magicPred)))
                magicPredicates.add(magicPred)
            else:
                prevPredicates.append(pred)
                
        #Modify rules
        #we modify the original rule by inserting
        #occurrences of the magic predicates corresponding
        #to the derived predicates of the body and to the head
        headMagicPred=rule.formula.head.makeMagicPred()
        idxIncrement=0
        newRule=copy.deepcopy(rule)
        for idx,(magicPred,origPred) in magicPositions.items():
            newRule.formula.body.formulae.insert(idx+idxIncrement,magicPred)
            idxIncrement+=1
        newRule.formula.body.formulae.insert(0,headMagicPred)
        newRules.append(newRule)
    if not newRules:
        print "No magic set candidates"
        if OWL_NS.InverseFunctionalProperty in factGraph.objects(predicate=RDF.type):
            newRules.extend(HornFromN3(StringIO(FUNCTIONAL_SEMANTCS)))
        if (None,OWL_NS.oneOf,None) in factGraph:
            #Only include list and oneOf semantics
            #if oneOf axiom is detected in graph 
            #reduce computational complexity
            newRules.extend(HornFromN3(StringIO(NOMINAL_SEMANTICS)))
    for rule in newRules:
        yield rule

def NormalizeGoals(goals):
    if isinstance(goals,(list,set)):
        for goal in goals:
            yield goal,{}
    elif isinstance(goals,tuple):
        yield sparqlQuery,{}
    else:
        print goals
        query=RenderSPARQLAlgebra(Parse(goals))
        for pattern in query.patterns:
            yield pattern[:3],query.prolog.prefixBindings
    
class AdornedRule(Rule):
    """Rule with 'bf' adornment and is comparable"""
    def __init__(self, clause, declare=None,nsMapping=None):
        decl=set()
        self.ruleStr=''
        for pred in itertools.chain(iterCondition(clause.head),
                                    iterCondition(clause.body)):
            decl.update([term for term in GetArgs(pred) if isinstance(term,Variable)])
            self.ruleStr+=''.join(pred.toRDFTuple())
        super(AdornedRule, self).__init__(clause,decl,nsMapping)        

    def __hash__(self):
        return hash(self.ruleStr)
        
    def __eq__(self,other):
        return hash(self) == hash(other)   

def GetArgs(term):
    if isinstance(term,N3Builtin):
        return term.argument
    elif isinstance(term,Uniterm):
        return term.arg
    else:
        raise term        

def GetOp(term):
    if isinstance(term,N3Builtin):
        return term.uri
    elif isinstance(term,Uniterm):
        return term.op
    else:
        print term
        raise term        

def NormalizeUniterm(term):
    if isinstance(term,Uniterm):
        return term
    elif isinstance(term,N3Builtin):
        return Uniterm(term.uri,term.argument) 
    
def AdornRule(derivedPreds,clause,newHead):
    """
    Adorns a horn clause using the given new head and list of
    derived predicates
    """
    assert len(list(iterCondition(clause.head)))==1
    sip=BuildNaturalSIP(clause,derivedPreds)
    bodyPredReplace={}
    for literal in iterCondition(sip.sipOrder):
        args = GetArgs(literal)
        op   = GetOp(literal)
        if op in derivedPreds:
            for N,x in IncomingSIPArcs(sip,op): 
                if not set(x).difference(args):
                    # A binding
                    # for q is useful, however, only if it is a binding for an argument of q.
                    bodyPredReplace[literal]=AdornedUniTerm(NormalizeUniterm(literal),
                            [ i in x and 'b' or 'f' for i in args])
    rule=AdornedRule(Clause(And([bodyPredReplace.get(p,p) 
                                 for p in iterCondition(sip.sipOrder)]),
                            AdornedUniTerm(clause.head,newHead.adornment)))
    rule.sip = sip
    return rule

def GetOp(term):
    return term.op == RDF.type and term.arg[-1] or term.op

def AdornProgram(factGraph,rs,goals,derivedPreds=None):
    """
    The process starts from the given query. The query determines bindings for q, and we replace
    q by an adorned version, in which precisely the positions bound in the query are designated as
    bound, say q e . In general, we have a collection of adorned predicates, and as each one is processed,
    we will mark it, so that it will not be processed again. If p a is an unmarked adorned
    predicate, then for each rule that has p in its head, we generate an adorned version for the rule
    and add it to Pad; then p is marked as processed.    
    
    The adorned version of a rule contains additional
    adorned predicates, and these are added to the collection, unless they already appear
    there. The process terminates when no unmarked adorned predicates are left.
        
    >>> ruleStore,ruleGraph=SetupRuleStore(StringIO(PROGRAM2))
    >>> ruleStore._finalize()
    >>> fg=Graph().parse(StringIO(PROGRAM2),format='n3')
    >>> rs,query=AdornProgram(fg,ruleGraph,NON_LINEAR_MS_QUERY)
    >>> for rule in rs: print rule
    Forall ?Y ?X ( ex:sg(?X ?Y) :- ex:flat(?X ?Y) )
    Forall ?Y ?Z4 ?X ?Z1 ?Z2 ?Z3 ( ex:sg(?X ?Y) :- And( ex:up(?X ?Z1) ex:sg(?Z1 ?Z2) ex:flat(?Z2 ?Z3) ex:sg(?Z3 ?Z4) ex:down(?Z4 ?Y) ) )
    >>> print query
    (rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#john'), rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#sg'), ?X)
    """
    from FuXi.DLP import LloydToporTransformation
#    rs=rs is None and Ruleset(n3Rules=ruleGraph.store.rules,
#               nsMapping=ruleGraph.store.nsMgr) or rs
    unprocessedAdornedPreds = []
    for goal,nsBindings in NormalizeGoals(goals):
        print goal,nsBindings
        unprocessedAdornedPreds.append(AdornLiteral(goal,nsBindings))
        
    if not derivedPreds:
        derivedPreds=list(DerivedPredicateIterator(factGraph,rs))
    adornedProgram=set()
    markedPreds=[]
    
    def processedAdornedPred(pred,_list):
        for p in _list:
            if GetOp(p) == GetOp(pred) and p.adornment == pred.adornment:
                return True
        return False
    
    while unprocessedAdornedPreds:
        term=unprocessedAdornedPreds.pop()
        markedPreds.append(term)
        #check if there is a rule with term as its head
        for rule in rs:
            for clause in LloydToporTransformation(rule.formula):
                head=clause.head
                _a=GetOp(head)
                _b=GetOp(term)
                if isinstance(head,Uniterm) and GetOp(head) == GetOp(term):
                    #for each rule that has p in its head, we generate an adorned version for the rule
                    # print rule, term
    #                print "\t",rule
                    adornedRule=AdornRule(derivedPreds,clause,term)
                    adornedProgram.add(adornedRule)
                    #The adorned version of a rule contains additional adorned
                    #predicates, and these are added
                    for pred in iterCondition(adornedRule.formula.body):
                        if isinstance(pred,AdornedUniTerm) and not processedAdornedPred(pred,markedPreds):
                            unprocessedAdornedPreds.append(pred)
                            markedPreds.append(pred)
    return adornedProgram

class AdornedUniTerm(Uniterm):
    def __init__(self,uterm,adornment=None):
        self.adornment=adornment
        self.nsMgr=uterm.nsMgr
        newArgs=copy.deepcopy(uterm.arg)
        super(AdornedUniTerm, self).__init__(uterm.op,newArgs)
        self.isMagic=False
        
    def makeMagicPred(self):
        """
        Make a (cloned) magic predicate
        
        The arity of the new predicate is the number of occurrences of b in the 
        adornment a, and its arguments correspond to the bound arguments of p a
        """
        newAdornedPred=AdornedUniTerm(self,self.adornment)
        if self.op == RDF.type:
            newAdornedPred.arg[-1] = URIRef(self.arg[-1]+'_magic')
        elif len([i for i in self.adornment if i =='b'])==1:
            #adorned predicate occurrence with one out of two arguments bound
            #converted into a magic predicate: It becomes a unary predicate 
            #(an rdf:type assertion)
            newAdornedPred.arg[-1] = URIRef(self.op+'_magic')
            newAdornedPred.arg[0] = [self.arg[idx] 
                                        for idx,i in enumerate(self.adornment) 
                                                if i =='b'][0]            
            newAdornedPred.op = RDF.type
        else:
            newAdornedPred.op=URIRef(self.op+'_magic')
        newAdornedPred.isMagic=True
        return newAdornedPred

    def __hash__(self):
        return self._hash ^ hash(reduce(lambda x,y:x+y,self.adornment))
        
    # def __eq__(self,other):
    #     return self.adornment==other.adornment and\
    #            self.op==other.op and\
    #            self.arg==other.arg
                
    def getDistinguishedVariables(self):
        for idx,term in enumerate(self.arg):
            if self.adornment[idx]=='b' and isinstance(term,Variable):
                yield term
                
    def getBindings(self,uniterm):
        rt={}
        for idx,term in enumerate(self.arg):
            goalArg=self.arg[idx]
            candidateArg=uniterm.arg[idx]
            if self.adornment[idx]=='b' and isinstance(candidateArg,Variable):
                #binding
                rt[candidateArg]=goalArg
        return rt
        
    def toRDFTuple(self):
        if hasattr(self,'isMagic') and self.isMagic:
            return (self.arg[0],self.op,self.arg[-1])
        else:
            subject,_object = self.arg
            return (subject,self.op,_object)
                
    def __repr__(self):
        pred = self.normalizeTerm(self.op)
        adornSuffix='_'+''.join(self.adornment)
        adornSuffix = self.op == RDF.type and '_b' or adornSuffix
        if self.isMagic:
            if self.op == RDF.type:
                return "%s(%s)"%(self.normalizeTerm(self.arg[-1]),
                                 self.normalizeTerm(self.arg[0]))
            else:
                return "%s(%s)"%(pred,
                                ' '.join([self.normalizeTerm(i) 
                                            for idx,i in enumerate(self.arg) 
                                                    if self.adornment[idx]=='b']))
        elif self.op == RDF.type:
            return "%s%s(%s)"%(self.normalizeTerm(self.arg[-1]),
                               adornSuffix,
                               self.normalizeTerm(self.arg[0]))
        else:
            return "%s%s(%s)"%(pred,
                               adornSuffix,
                               ' '.join([self.normalizeTerm(i) for i in self.arg]))

def AdornLiteral(rdfTuple,newNss=None):
    """
    An adornment for an n-ary predicate p is a string a of length n on the 
    alphabet {b, f}, where b stands for bound and f stands for free. We 
    assume a fixed order of the arguments of the predicate.
    
    Intuitively, an adorned occurrence of the predicate, p a, corresponds to a 
    computation of the predicate with some arguments bound to constants, and 
    the other arguments free, where the bound arguments are those that are
    so indicated by the adornment.    
    
    >>> EX=Namespace('http://doi.acm.org/10.1145/6012.15399#')
    >>> query=RenderSPARQLAlgebra(Parse(NON_LINEAR_MS_QUERY))
    >>> literal=query.patterns[0][:3]
    >>> literal
    (rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#john'), rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#sg'), ?X)
    >>> aLit=AdornLiteral(literal,query.prolog.prefixBindings)
    >>> aLit
    mst:sg_bf(mst:john ?X)
    >>> aLit.adornment
    ['b', 'f']
    >>> aLit.getBindings(Uniterm(EX.sg,[Variable('X'),EX.jill]))
    {?X: rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#john')}
    """
    args=[rdfTuple[0],rdfTuple[-1]]
    newNss=newNss is None and {} or newNss
    uTerm = BuildUnitermFromTuple(rdfTuple,newNss)
    opArgs=rdfTuple[1] == RDF.type and [args[-1]] or args
    adornment=[ isinstance(term,(Variable,BNode)) and 'f' or 'b' 
                for idx,term in enumerate(opArgs) ]
    return AdornedUniTerm(uTerm,adornment)  

def iterCondition(condition):
    return isinstance(condition,SetOperator) and condition or iter([condition])

def DerivedPredicateIterator(factsOrBasePreds,ruleset):
    """
    >>> ruleStore,ruleGraph=SetupRuleStore()
    >>> g=ruleGraph.parse(StringIO(MAGIC_PROGRAM1),format='n3')
    >>> ruleStore._finalize()
    >>> ruleFacts=Graph().parse(StringIO(MAGIC_PROGRAM1),format='n3')
    >>> for lit in DerivedPredicateIterator(ruleFacts,ruleGraph): print lit
    ex:anc(?X ?Y)
    >>> ruleStore,ruleGraph=SetupRuleStore()
    >>> g=ruleGraph.parse(StringIO(PROGRAM2),format='n3')
    >>> ruleStore._finalize()
    >>> ruleFacts=Graph().parse(StringIO(PROGRAM2),format='n3')    
    >>> for lit in DerivedPredicateIterator(ruleFacts,ruleGraph): print lit
    ex:sg(?X ?Y)
    """
    basePreds=[GetOp(buildUniTerm(fact)) for fact in factsOrBasePreds 
                        if fact[1] != LOG.implies]     
    processed={True:set(),False:set()}
    derivedPreds=set()
    uncertainPreds=set()
    ruleBodyPreds=set()
    ruleHeads=set()
    for rule in ruleset:
        for idx,term in enumerate(itertools.chain(iterCondition(rule.formula.head),
                                  iterCondition(rule.formula.body))):
            op = GetOp(term)
            if op not in processed[idx>0]: 
                if idx > 0:
                    ruleBodyPreds.add(op)
                else:
                    ruleHeads.add(op)
#                assert op not in basePreds or idx > 0,"Malformed program!"
                if op in basePreds:
                    uncertainPreds.add(op)
                else:
                    if idx == 0 and not isinstance(op,Variable):
                        derivedPreds.add(op)
                    elif not isinstance(op,Variable):
                        uncertainPreds.add(op)
                processed[idx>0].add(op)
    for pred in uncertainPreds:
        if (pred not in ruleBodyPreds and not isinstance(pred,Variable)) or\
           pred in ruleHeads:
            derivedPreds.add(pred)
#    assert not derivedPred.intersection(basePreds),"There are predicates that are both derived and base!"
    for pred in derivedPreds:
        yield pred
    
def IsBasePredicate(ruleGraph,pred):
    pass

def iter_non_base_non_derived_preds(ruleset,intensional_db):
    rt=set()
    intensional_preds=set([p for p in intensional_db.predicates() 
                                    if p != LOG_NS.implies])
    for rule in ruleset:
        for uterm in rule.formula.head:
            if uterm.op in intensional_preds and uterm.op not in rt:
                rt.add(uterm.op)
                yield uterm.op, (fact 
                         for fact in intensional_db.triples((None,uterm.op,None)))

def NormalizeLPDb(ruleGraph,fact_db):
    """
    For performance reasons, it 1s good to decompose the database into a set of
    pure base predicates (which can then be stored using a standard DBMS)
    and a set of pure derived predicates Fortunately, such a decomposition 1s 
    always possible, because every database can be rewritten as an ‚Äö√Ñ√∂‚àö√ë‚àö‚àÇ‚Äö√†√∂‚àö√´‚Äö√†√∂‚Äö√†¬¥equivalent‚Äö√Ñ√∂‚àö√ë‚àö‚àÇ‚Äö√†√∂‚àö√´‚Äö√†√∂≈ì√Ñ
    database containing only base and derived predicates.    
    
    >>> ruleStore,ruleGraph=SetupRuleStore()
    >>> g=ruleGraph.parse(StringIO(PARTITION_LP_DB_PREDICATES),format='n3')
    >>> ruleStore._finalize()    
    >>> len(ruleStore.rules)
    1
    >>> factGraph=Graph().parse(StringIO(PARTITION_LP_DB_PREDICATES),format='n3')
    >>> rs=Ruleset(n3Rules=ruleStore.rules,nsMapping=ruleStore.nsMgr)
    >>> for i in rs: print i
    Forall ?Y ?X ?Z ( ex:grandfather(?X ?Y) :- And( ex:father(?X ?Z) ex:parent(?X ?Y) ) )
    >>> len(factGraph)
    4
    >>> print [p for p,iter in iter_non_base_non_derived_preds(rs,factGraph)]
    [rdflib.URIRef('http://doi.acm.org/10.1145/16856.16859#grandfather')]
    """
    candidatePreds=False
    rs=Ruleset(n3Rules=ruleGraph.store.rules,
               nsMapping=ruleStore.nsMgr)
    toAdd=[]
    for pred,replFacts in iter_non_base_non_derived_preds(rs,fact_db):
        replPred=URIRef(pred+'_ext')
        for s,p,o in replFacts:
            fact_db.remove((s,p,o))
            toAdd.append((s,replPred,o))
        head=Uniterm(pred,pred.arg)
        body=Uniterm(replPred,pred.arg)
        newRule=Rule(Clause(body,head),
                     [term for term in pred.arg if isinstance(term,Variable)])
        rs.append(newRule)
    return rs

class AdornProgramTest(unittest.TestCase):
    def setUp(self):
        self.ruleStore,self.ruleGraph=SetupRuleStore(StringIO(PROGRAM2))
        self.ruleStore._finalize()
        self.ruleStrings=[
        'Forall ?Y ?X ( _5:sg_bf(?X ?Y) :- And( _5:sg_magic(?X) ex:flat(?X ?Y) ) )',
        'Forall  ( _5:sg_magic(?Z1) :- And( _5:sg_magic(?X) ex:up(?X ?Z1) ) )',
        'Forall ?Z4 ?Y ?X ?Z1 ?Z2 ?Z3 ( _5:sg_bf(?X ?Y) :- And( _5:sg_magic(?X) ex:up(?X ?Z1) _5:sg_magic(?Z1) _5:sg_bf(?Z1 ?Z2) ex:flat(?Z2 ?Z3) _5:sg_magic(?Z3) _5:sg_bf(?Z3 ?Z4) ex:down(?Z4 ?Y) ) )',
        'Forall  ( _5:sg_magic(?Z3) :- And( _5:sg_magic(?X) ex:up(?X ?Z1) _5:sg_bf(?Z1 ?Z2) ex:flat(?Z2 ?Z3) ) )',
        ]

    def testAdorn(self):
        fg=Graph().parse(StringIO(PROGRAM2),format='n3')
        rules=Ruleset(n3Rules=self.ruleGraph.store.rules,
                   nsMapping=self.ruleStore.nsMgr)
        from pprint import pprint;pprint(self.ruleStrings)        
        for rule in MagicSetTransformation(fg,
                                           rules,
                                           NON_LINEAR_MS_QUERY,
                                           [MAGIC.sg]):
            self.failUnless(repr(rule) in self.ruleStrings, repr(rule.formula))
        
def buildMagicBody(N,prevPredicates,adornedHead,derivedPreds):
    body=[adornedHead.makeMagicPred()]
    for prevAPred in prevPredicates:
        op = GetOp(prevAPred)
        if op in N:
            #If qj, j<i, is in N, we add qj to the body of the magic rule
            body.append(prevAPred)
        if op in derivedPreds and prevAPred.adornment.count('b')>0:
            #If qj is a derived predicate and its adornment contains at least 
            #one b, we also add the corresponding magic predicate to the body
            body.append(prevAPred.makeMagicPred())
    return body
            
def test():
    unittest.main()    
    # import doctest
    # doctest.testmod()

if __name__ == '__main__':
    test()