import unittest, os, time, sys 
from cStringIO import StringIO 
from rdflib import RDF, URIRef 
from FuXi.Rete import * 
from FuXi.Rete.RuleStore import N3RuleStore 
from FuXi.Rete.Util import renderNetwork, generateTokenSet 
from FuXi.Horn.PositiveConditions import Uniterm, BuildUnitermFromTuple 
from FuXi.Horn.HornRules import HornFromN3 
from rdflib import plugin 
from rdflib.store import Store 
from rdflib.Graph import Graph 
N3_PROGRAM=\
""" 
@prefix m: <http://example.com/#>. 
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> . 
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . 
{ ?det a m:Detection. 
  ?det has m:name ?infName. 
} => { 

  ?det has m:inference [ a m:Inference; m:inference_name ?infName ]. 
}. 

""" 
N3_FACTS=\
""" 
@prefix m: <http://example.com/#>. 
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> . 
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . 
m:Detection a rdfs:Class. 
m:Inference a rdfs:Class. 
:det1 a m:Detection. 
:det1 m:name "Inference1". 
:det2 a m:Detection. 
:det2 m:name "Inference2". 
""" 
class ExistentialInHeadTest(unittest.TestCase): 
    def testExistentials(self): 
        store = plugin.get('IOMemory',Store)() 
        store.open('') 
        ruleStore = N3RuleStore() 
        ruleGraph = Graph(ruleStore) 
        ruleGraph.parse(StringIO(N3_PROGRAM),format='n3') 
        factGraph = Graph(store) 
        factGraph.parse(StringIO(N3_FACTS),format='n3') 
        deltaGraph = Graph(store) 
        network = ReteNetwork(ruleStore, 
                              initialWorkingMemory=generateTokenSet(factGraph), 
                              inferredTarget = deltaGraph) 
        inferenceCount = 0 
        for inferredFact in network.inferredFacts.subjects(
                                       predicate=RDF.type, 
                                       object=URIRef('http://example.com/#Inference')): 
            inferenceCount = inferenceCount + 1 
        self.failUnless(inferenceCount > 1,  'Each rule firing should introduce a new BNode!') 
        cg = network.closureGraph(factGraph, store=ruleStore) 
        print cg.serialize(format="n3") 
if __name__ == "__main__": 
    unittest.main() 