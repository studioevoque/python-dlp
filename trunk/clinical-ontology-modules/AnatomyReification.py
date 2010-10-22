"""
>>> g = Graph()
>>> g.bind('ro',RO)
>>> g.bind('fma',FMA)
>>> s=set()
>>> heartWall = FMA['FMA_7274']
>>> heartWallTerm = FMAAnatomyTerm(heartWall)
>>> s.add(heartWallTerm)
>>> s.add(FMAAnatomyTerm(heartWall))
>>> len(s)
1
>>> heartWallPartTerm = SomePartOfAnatomy(heartWallTerm)
>>> heartWallPartTerm.makeClass(g)
( ro:part_of some fma:FMA_7274 )
>>> s.add(heartWallPartTerm)
>>> len(s)
2
>>> myocardium = FMA['FMA_9462']
>>> s.add(LogicalAnatomyDisjunction([myocardium,heartWall]))
>>> s.add(LogicalAnatomyDisjunction([myocardium,heartWall]))
>>> len(s)
3
"""
from rdflib.Graph import Graph
from rdflib import RDF, OWL, RDFS, URIRef, Literal
from FuXi.Syntax.InfixOWL import *
from rdflib.Namespace import Namespace

RO     = Namespace('http://purl.org/obo/owl/obo#')
FMA    = Namespace('http://purl.org/obo/owl/FMA#')

def MakeName(label,termId):
    return 'fma:%s'%(label and label or termId.split(FMA)[-1])

class HashableComparableThing(object):
    def __eq__(self, other):
        return hash(self) == hash(other)

def DepthFirstTraversal(term):
    assert isinstance(term,HashableComparableThing)
    if isinstance(term,(SomePartOfAnatomy,FMAAnatomyTerm)):
        yield term
    elif isinstance(term,LogicalAnatomyDisjunction):
        for descendent in term:
            for leaf in DepthFirstTraversal(descendent):
                yield leaf

CIRCUM_QUERY1=\
"""
SELECT ?CLS 
{ 
    ?CLS rdfs:subClassOf 
      [ owl:onProperty ro:has_part;
        owl:someValuesFrom ?FILLER ]
    OPTIONAL {
        ?FILLER rdfs:subClassOf [
            owl:onProperty ro:part_of ?ANCESTOR
        ]
        FILTER(?ANCESTOR = ?CLS)
    }
    Filter(!BOUND(?ANCESTOR))
}"""

class FMAAnatomyTerm(HashableComparableThing):
    def __init__(self, identifier, label = None):
        self.label      = label
        self.identifier = identifier
        
    def __repr__(self):
        return MakeName(self.label,self.identifier) 
        
    def __hash__(self):
        return hash(self.identifier)
    
    def CircumTranverse(self,graph):
        for parent in graph.query(CIRCUM_QUERY1,
                                  initBindings={Variable('FILLER'):
                                                self.cls},
                                  initNs={u'ro':RO}):
            yield parent
            for gParent in FMAAnatomyTerm(parent).CircumTranverse(graph):
                yield gParent    

    def makeClass(self,graph):
        cl = Class(self.identifier,graph=graph)
        if self.label:
            cl.label = Literal(self.label)
        return cl
    
class SomePartOfAnatomy(HashableComparableThing):
    def __init__(self, term):
        self.term = term

    def __repr__(self):
        return '(part_of some %s)'%MakeName(self.term.label,
                                            self.term.identifier) 
        
    def __hash__(self):
        return hash(u"PartOf"+self.term.identifier)
    
    def makeClass(self,graph):
        return Property(RO['part_of'],graph=graph)|some|self.term.makeClass(graph)
        
def HashOfTermOrDisjunction(item):
    if isinstance(item,LogicalAnatomyDisjunction):
        return hash(reduce(lambda x,y:hash(x)^hash(y),
                           item))
    else:
        return hash(item)    
    
class LogicalAnatomyDisjunction(HashableComparableThing):
    def __init__(self, members):
        self.members = [m for m in members]
        self._hash = HashOfTermOrDisjunction(self)

    def __iter__(self):
        for item in self.members:
            yield item

    def __repr__(self):
        return '(%s)'%(' or '.join([repr(i) for i in self.members])) 

    def __hash__(self):
        return self._hash
    
    def makeClass(self,graph):
        return BooleanClass(operator=OWL_NS.unionOf,
                            members=[m.makeClass(graph) for m in self.members])    
    
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()    