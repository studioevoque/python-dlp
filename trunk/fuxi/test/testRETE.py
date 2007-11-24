from pprint import pprint
from sets import Set
from FuXi.Rete import *
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.BetaNode import PartialInstanciation, LEFT_MEMORY, RIGHT_MEMORY
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import renderNetwork,generateTokenSet, xcombine
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef,Literal,Variable
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
import unittest

RDFLIB_CONNECTION=''
RDFLIB_STORE='IOMemory'

CWM_NS    = Namespace("http://cwmTest/")
DC_NS     = Namespace("http://purl.org/dc/elements/1.1/")
STRING_NS = Namespace("http://www.w3.org/2000/10/swap/string#")
MATH_NS   = Namespace("http://www.w3.org/2000/10/swap/math#")
FOAF_NS   = Namespace("http://xmlns.com/foaf/0.1/") 
OWL_NS    = Namespace("http://www.w3.org/2002/07/owl#")
TEST_NS   = Namespace("http://metacognition.info/FuXi/DL-SHIOF-test.n3#")
TEST2_NS  = Namespace("http://metacognition.info/FuXi/filters.n3#")
LOG       = Namespace("http://www.w3.org/2000/10/swap/log#")

queryNsMapping={'test':'http://metacognition.info/FuXi/test#',
                'rdf':'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
                'foaf':'http://xmlns.com/foaf/0.1/',
                'dc':'http://purl.org/dc/elements/1.1/',
                'rss':'http://purl.org/rss/1.0/',
                'rdfs':'http://www.w3.org/2000/01/rdf-schema#',
                'rdf':'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
                'owl':OWL_NS,
                'rdfs':RDFS,
}

nsMap = {
  u'rdfs':RDFS.RDFSNS,
  u'rdf' :RDF.RDFNS,
  u'rete':RETE_NS,
  u'owl' :OWL_NS,
  u''    :TEST_NS,
  u'foaf':URIRef("http://xmlns.com/foaf/0.1/"),
  u'math':URIRef("http://www.w3.org/2000/10/swap/math#"),
}

testHarness = {
    'DL Test': [
      [('DL-SHIOF-test.n3','n3'),],
      [],
      [
        (TEST_NS.Nozze_di_Figaro,RDF.type,TEST_NS.DaPonteOperaOfMozart),
        (TEST_NS.Don_Giovanni,RDF.type,TEST_NS.DaPonteOperaOfMozart),
        (TEST_NS.Cosi_fan_tutte,RDF.type,TEST_NS.DaPonteOperaOfMozart),
#        (TEST_NS.Lion,RDF.type,TEST_NS.LivingBeing),
#        (TEST_NS.marge,RDF.type,TEST_NS.Human),
#        (TEST_NS.maggie,TEST_NS.child,TEST_NS.marge),
#        (TEST_NS.bart,OWL_NS.sameAs,TEST_NS.b),
#        (TEST_NS.marge,TEST_NS.knows,TEST_NS.smithers),
      ],
      [
       #(TEST_NS.Cosi_fan_tutte,RDF.type,TEST_NS.DaPonteOperaOfMozart)
        #(TEST_NS.bart,TEST_NS.name,Literal("Bart Simpson")),
      ]
    ],
#    'Built-ins test': [
#      [('filters.n3','n3'),],
#      [],
#      [
#        (TEST2_NS.b,RDF.type,TEST2_NS.Selected),
#        (TEST2_NS.c,RDF.type,TEST2_NS.Selected2),
#        (TEST2_NS.b,TEST2_NS.smallerVal,Literal(1)),
#      ],
#     [
#        #(TEST2_NS.c,TEST2_NS.prop1,Literal(7)),
#     ]
#    ]
#    'test': [
#      [('test.n3','n3'),],
#      [],
#      [
#        (URIRef('http://www.w3.org/2002/03owlt/InverseFunctionalProperty/premises003#inv'),
#         RDF.type,
#         OWL_NS.FunctionalProperty),        
#      ],
#     []
#    ]    
}

class TestEvaluateNetwork(unittest.TestCase):
    def testRules(self):
        store = plugin.get(RDFLIB_STORE,Store)()        
        for ruleGraphs,factGraphs,inferredTriples,debugTriples in testHarness.values():
            store.open(RDFLIB_CONNECTION)
            ruleStore=N3RuleStore()
            ruleGraph = Graph(ruleStore)            
            closureDeltaGraph = Graph(store) 
            for fileN,format in ruleGraphs:
                ruleGraph.parse(open(fileN),format=format)
            if factGraphs:
                factGraph = Graph(store)
                for fileN,format in factGraphs:
                    if (fileN,format) not in ruleGraphs:                
                        factGraph.parse(open(fileN),format=format)
            else:
                factGraph = Graph(store)
                for fileN,format in ruleGraphs:
                    factGraph.parse(open(fileN),format=format)
            if debugTriples:
                workingMemory = generateTokenSet(factGraph,debugTriples)
            else:
                workingMemory = generateTokenSet(factGraph)
            pprint([item.asTuple() for item in workingMemory])
            network = ReteNetwork(ruleStore,
                                  initialWorkingMemory=workingMemory,
                                  inferredTarget = closureDeltaGraph,
                                  nsMap = nsMap,
                                  graphVizOutFile = 'rete-network.dot')
            for termNode in network.terminalNodes:
                lhsF,rhsF = termNode.ruleFormulae
                print termNode
                print "\t%s instanciations"%network.instanciations[termNode]
#                print "### left memory ###"
#                pprint(list(termNode.memories[LEFT_MEMORY]))
#                print "###################"
#                print "### right memory ###"
#                pprint(list(termNode.memories[RIGHT_MEMORY]))
#                print "####################"
#            pprint(list(network.inferredFacts))
            for triple in inferredTriples:
                if not triple in factGraph and triple not in network.inferredFacts:#,"missing triple %s"%(repr(triple)):
                    print network.inferredFacts.serialize(format='n3')
                    print triple
                    raise
            store.rollback()

class OpenTest(unittest.TestCase):
    def testCreateNetwork(self):
        store = plugin.get(RDFLIB_STORE,Store)()
        store.open(RDFLIB_CONNECTION)
        ruleStore=N3RuleStore()
        ruleGraph = Graph(ruleStore)            
        closureDeltaGraph = Graph(store) 
        ruleGraph.parse(open('pD-rules.n3'),format='n3')
#        factGraph = Graph(store)
#        factGraph.parse(open('test.n3'),format='n3')
        network = ReteNetwork(ruleStore,nsMap = nsMap,graphVizOutFile = 'test-network-build.dot')
        for key,value in network.alphaPatternHash.items():
            print "### %s ###"%(repr(key))
            for key2,values in value.items():
                print "\t### %s ###"%(repr(key2))
                pprint(values)
        store.rollback()
                
if __name__ == '__main__':
    suite = unittest.makeSuite(TestEvaluateNetwork)
    unittest.TextTestRunner(verbosity=5).run(suite)
#    suite = unittest.makeSuite(OpenTest)
#    unittest.TextTestRunner(verbosity=0).run(suite)
