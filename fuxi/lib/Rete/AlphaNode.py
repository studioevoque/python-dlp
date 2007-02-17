"""
This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 2.5 License.
To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-sa/2.5/ 
or send a letter to Creative Commons, 543 Howard Street, 5th Floor, San Francisco, California, 94105, USA.
"""
from RuleStore import N3Builtin
from rdflib import Variable, BNode,RDF,Variable,Literal,RDFS, URIRef, Namespace
from rdflib.Graph import Graph 
from sets import Set
from ReteVocabulary import RETE_NS
from BuiltinPredicates import FILTERS, FUNCTIONS
from Node import Node

OWL_NS    = Namespace("http://www.w3.org/2002/07/owl#")

SUBJECT   = 0
PREDICATE = 1
OBJECT    = 2

VARIABLE = 0
VALUE    = 1

TERMS = [SUBJECT,PREDICATE,OBJECT]

def normalizeTerm(term):
    """
    Graph Identifiers are used
    """
    if isinstance(term,Graph):
        return term.identifier
    else:
        return term

class ReteToken:
    """
    A ReteToken, an RDF triple in a Rete network.  Once it passes an alpha node test,
    if will have unification substitutions per variable
    """
    def __init__(self,(subject,predicate,object_),debug = False):
        self.debug = debug
        self.subject   = (None,normalizeTerm(subject))
        self.predicate = (None,normalizeTerm(predicate))
        self.object_   = (None,normalizeTerm(object_))
        self.bindingDict = {}
        self._termConcat = self.concatenateTerms()
        self.hash = hash(self._termConcat) 
        self.divergentVariables = {}

    def __hash__(self):
        """
        
        >>> token1 = ReteToken((RDFS.domain,RDFS.domain,RDFS.Class))
        >>> token2 = ReteToken((RDFS.domain,RDFS.domain,RDFS.Class))
        >>> token1 == token2
        True
        >>> token1 in Set([token2])
        True
        """
        return self.hash 

    def concatenateTerms(self):
        return reduce(lambda x,y:x+y,[term[VALUE] for term in [self.subject,self.predicate,self.object_]])

    def __eq__(self,other):
        return hash(self) == hash(other)   

    def alphaNetworkHash(self,termHash):
        """
        We store pointers to all the system's alpha memories in a hash table, indexed
        according to the particular values being tested. Executing the alpha network then becomes a
        simple matter of doing eight hash table lookups:

        >>> aNode1 = AlphaNode((Variable('Z'),RDF.type,Variable('A')))
        >>> aNode2 = AlphaNode((Variable('X'),RDF.type,Variable('C')))
        >>> token = ReteToken((URIRef('urn:uuid:Boo'),RDF.type,URIRef('urn:uuid:Foo')))
        >>> token.alphaNetworkHash(aNode1.alphaNetworkHash())
        u'http://www.w3.org/1999/02/22-rdf-syntax-ns#type'
                
        """
        triple = list(self.asTuple())
        termHash = list(termHash)
        return ''.join([triple[idx] for idx in TERMS if termHash[idx] == '1'])        
                
    def unboundCopy(self,noSubsequentDebug=False):
        if noSubsequentDebug:
            return ReteToken((self.subject[VALUE],self.predicate[VALUE],self.object_[VALUE]))
        else:
            return ReteToken((self.subject[VALUE],self.predicate[VALUE],self.object_[VALUE]),self.debug)
                
    def __repr__(self):        
        return "<ReteToken: %s>"%(
            ','.join(["%s->%s"%(var,val) for var,val in [self.subject,self.predicate,self.object_] if isinstance(var,(Variable,BNode))])
        )
            
    def asTuple(self):
        return (self.subject[VALUE],self.predicate[VALUE],self.object_[VALUE])
        
    def bindVariables(self,alphaNode):
        """
        This function, called when a token passes a node test, associates token terms with variables
        in the node test 
        """
        self.pattern = alphaNode.triplePattern
        self.subject   = (alphaNode.triplePattern[SUBJECT],self.subject[VALUE])
        self.predicate = (alphaNode.triplePattern[PREDICATE],self.predicate[VALUE])
        self.object_   = (alphaNode.triplePattern[OBJECT],self.object_[VALUE])
        assert not self.bindingDict,self.bindingDict
        bindHashItems = []
        for var,val in [self.subject,self.predicate,self.object_]:
            if var and isinstance(var,(Variable,BNode)) and var not in self.bindingDict:
                self.bindingDict[var] = val
                bindHashItems.append(var + val)
            else:
                bindHashItems.append(val)
        self.hash = hash(reduce(lambda x,y:x+y,bindHashItems))
        if len(self.bindingDict.values()) != len(Set(self.bindingDict.values())):
            for key,val in self.bindingDict.items():
                self.divergentVariables.setdefault(val,[]).append(key)
            for val,keys in self.divergentVariables.items():
                if len(keys) == 1:
                    del self.divergentVariables[val]
        return self            
    
def defaultIntraElementTest(aReteToken,triplePattern):
    """
    'Standard' Charles Forgy intra element token pattern test.
    """
    tokenTerms = [aReteToken.subject[VALUE],aReteToken.predicate[VALUE],aReteToken.object_[VALUE]]
    varBindings = {}
    for idx in [SUBJECT,PREDICATE,OBJECT]:
        tokenTerm   = tokenTerms[idx]
        patternTerm = triplePattern[idx]
        if not isinstance(patternTerm,(Variable,BNode)) and tokenTerm != patternTerm:
            return False            
        elif patternTerm in varBindings and varBindings[patternTerm] != tokenTerm:
            return False
        elif patternTerm not in varBindings:
            varBindings[patternTerm] = tokenTerm
    return True

class AlphaNode(Node):
    """
    Basic Triple Pattern Pattern check
    """
    def __init__(self,triplePatternOrFunc):
        self.relinked = False
        self.name = BNode()
        self.triplePattern = triplePatternOrFunc
        self.descendentMemory = []
        self.descendentBetaNodes = Set()
        self.builtin = bool(FUNCTIONS.get(self.triplePattern[PREDICATE]) or FILTERS.get(self.triplePattern[PREDICATE]))
        self.universalTruths = []

    def alphaNetworkHash(self,groundTermHash=False):
        """
        Thus, given a WME w, to determine which alpha memories w should be added to, we need only check whether
        any of these eight possibilities is actually present in the system.  (Some might not be present, since 
        there might not be any alpha memory corresponding to that particular combination of tests and 's.)
        
        0 - Variable
        1 - Ground term        
        
        >>> aNode1 = AlphaNode((Variable('P'),RDF.type,OWL_NS.InverseFunctionalProperty))
        >>> aNode2 = AlphaNode((Variable('X'),Variable('P'),Variable('Z')))
        >>> aNode1.alphaNetworkHash()
        ('0', '1', '1')
        >>> aNode2.alphaNetworkHash()
        ('0', '0', '0')
        >>> aNode1.alphaNetworkHash(groundTermHash=True)
        u'http://www.w3.org/1999/02/22-rdf-syntax-ns#typehttp://www.w3.org/2002/07/owl#InverseFunctionalProperty'
        """
        if groundTermHash:
            return ''.join([term for term in self.triplePattern if not isinstance(term,(BNode,Variable))])
        else:
            return tuple([isinstance(term,(BNode,Variable)) and '0' or '1' for term in self.triplePattern])

    def checkDefaultRule(self,defaultRules):
        """
        Check to see if the inter element test associated with this Alpha node may match
        the given 'default' conflict set.  If so, update universalTruths with the
        default conflict set token list which if matched, means the intra element test automatically
        passes
        """
        pass

    def __repr__(self):
        return "<AlphaNode: %s. Feeds %s beta nodes>"%(repr(self.triplePattern),len(self.descendentBetaNodes))

    def activate(self,aReteToken):
        from BetaNode import PartialInstanciation, LEFT_MEMORY, RIGHT_MEMORY, LEFT_UNLINKING
        #print aReteToken.asTuple()
        #aReteToken.debug = True
        aReteToken.bindVariables(self)
        for memory in self.descendentMemory:
            singleToken = PartialInstanciation([aReteToken],consistentBindings=aReteToken.bindingDict.copy())
#            print memory
#            print self
#            print self.descendentMemory
            if memory.position == LEFT_MEMORY:
                memory.addToken(singleToken)
            else:
                memory.addToken(aReteToken)                
            if memory.successor.leftUnlinkedNodes and len(memory) == 1 and LEFT_UNLINKING:
                #Relink left memory of successor
                from Util import renderNetwork
                from md5 import md5
                from datetime import datetime
                import os                                
                print "Re-linking %s"%(memory.successor)
                print "Re-linking triggered from %s"%(repr(self))
                for node in memory.successor.leftUnlinkedNodes:
                    print "\trelinking to ", node, " from ", memory.position
                    #aReteToken.debug = True
                    if node.unlinkedMemory is None:
                        assert len(node.descendentMemory) == 1,"%s %s %s"%(node,
                                                                        node.descendentMemory,
                                                                        memory.successor)                        
                        disconnectedMemory = list(node.descendentMemory)[0]                        
                        
                    else:
                        disconnectedMemory = node.unlinkedMemory
                        node.descendentMemory.append(disconnectedMemory)
                        node.unlinkedMemory = None
                    if aReteToken.debug:
                        print "\t reattached memory ",str(disconnectedMemory) 
                    memory.successor.memories[LEFT_MEMORY] = disconnectedMemory                    
                    node.descendentBetaNodes.add(memory.successor)
                    #print memory.successor.memories[LEFT_MEMORY]
                    memory.successor.propagate(RIGHT_MEMORY,aReteToken.debug,wme=aReteToken)                    
                    #node._activate(singleToken,aReteToken.debug)
                    #print "Activating re-linked node", node
                    #node.propagate(None,aReteToken.debug)
#                    if memory.position == LEFT_MEMORY:
#                        node.propagate(memory.position,aReteToken.debug,singleToken)
#                    else:
#                        node.propagate(memory.position,aReteToken.debug,wme=aReteToken)

#                if memory.successor.network:
#                    dtNow = datetime.now().isoformat()
#                    fName = dtNow.replace(':','-').replace('.','-')
#                    renderNetwork(memory.successor.network).write_graphviz(fName+'.dot')
#                    os.popen ('dot -Tsvg -o %s %s'%(fName+'.svg',fName+'.dot'),'r')
#                    os.remove(fName+'.dot')
#                    print fName
                
                #self.relinked = True
                memory.successor.leftUnlinkedNodes = Set()
            if aReteToken.debug:
                    print "Added %s to %s"%(aReteToken,memory.successor)
            if memory.successor.aPassThru or not memory.successor.checkNullActivation(memory.position):
                if aReteToken.debug:
                    print "Propagated from %s"%(self)
                    print aReteToken.asTuple()
                if memory.position == LEFT_MEMORY:
                    memory.successor.propagate(memory.position,aReteToken.debug,singleToken)
                else:
                    memory.successor.propagate(memory.position,aReteToken.debug,wme=aReteToken)
            else:
                if aReteToken.debug:
                    print "skipped null right activation of %s from %s"%(memory.successor,self)
                                
class BuiltInAlphaNode(AlphaNode):
    """
    An Alpha Node for Builtins which doesn't participate in intraElement tests
    """
    def __init__(self,n3builtin):
        self.name = BNode()
        self.n3builtin = n3builtin
        self.descendentMemory = []
        self.descendentBetaNodes = Set()
        self.universalTruths = []        
    
    def intraElementTest(self,aReteToken):
        pass    
    
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()    