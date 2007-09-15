from pprint import pprint, pformat
from sets import Set
from FuXi.Rete import *
from FuXi.DLP import MapDLPtoNetwork, non_DHL_OWL_Semantics
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.Proof import GenerateProof
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Horn.HornRules import Clause, Ruleset
from InfixOWL import Class
from FuXi.Rete.Util import renderNetwork,generateTokenSet
from FuXi.Horn.PositiveConditions import And, Or, Uniterm, Condition, Atomic,SetOperator, buildUniTerm
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
from glob import glob
from rdflib.sparql.bison import Parse
import unittest, os, time,sys

RDFLIB_CONNECTION=''
RDFLIB_STORE='IOMemory'

CWM_NS    = Namespace("http://cwmTest/")
DC_NS     = Namespace("http://purl.org/dc/elements/1.1/")
STRING_NS = Namespace("http://www.w3.org/2000/10/swap/string#")
MATH_NS   = Namespace("http://www.w3.org/2000/10/swap/math#")
FOAF_NS   = Namespace("http://xmlns.com/foaf/0.1/") 
OWL_NS    = Namespace("http://www.w3.org/2002/07/owl#")
TEST_NS   = Namespace("http://metacognition.info/FuXi/DL-SHIOF-test.n3#")
LOG       = Namespace("http://www.w3.org/2000/10/swap/log#")
RDF_TEST  = Namespace('http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#')
OWL_TEST  = Namespace('http://www.w3.org/2002/03owlt/testOntology#')

queryNsMapping={'test':'http://metacognition.info/FuXi/test#',
                'rdf':'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
                'foaf':'http://xmlns.com/foaf/0.1/',
                'dc':'http://purl.org/dc/elements/1.1/',
                'rss':'http://purl.org/rss/1.0/',
                'rdfs':'http://www.w3.org/2000/01/rdf-schema#',
                'rdf':'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
                'owl':OWL_NS,
                'rdfs':RDF.RDFNS,
}

WITCH = Namespace('http://www.w3.org/2000/10/swap/test/reason/witch#')
DAN=Namespace('http://www.w3.org/2000/10/swap/test/reason/dan_home#')

nsMap = {
  u'rdfs' :RDFS.RDFSNS,
  u'rdf'  :RDF.RDFNS,
  u'rete' :RETE_NS,
  u'owl'  :OWL_NS,
  u''     :TEST_NS,
  u'otest':OWL_TEST,
  u'rtest':RDF_TEST,
  u'witch':WITCH,
  u'foaf' :URIRef("http://xmlns.com/foaf/0.1/"),
  u'math' :URIRef("http://www.w3.org/2000/10/swap/math#"),
}

class TestProof(unittest.TestCase):
    
    def createRuleStore(self,ruleGraphPath):
        ruleStore=N3RuleStore()
        Graph(ruleStore).parse(ruleGraphPath,format='n3')
        return ruleStore
    
    def setUp(self):
        store = plugin.get(RDFLIB_STORE,Store)()
        store.open(RDFLIB_CONNECTION)
        self.nsMapping = [('witch',WITCH),('dan',DAN)]
                
    def testMetacognition(self):
        g=Graph()
        g.parse('http://purl.org/net/chimezie/foaf')
        g.parse('http://xmlns.com/foaf/spec/')
        goal=(URIRef('http://flickr.com/photos/45452910@N00/21945461/'),
              RDF.type,
              FOAF_NS.Image)
        ruleStore=self.createRuleStore(StringIO(non_DHL_OWL_Semantics))
        network = ReteNetwork(ruleStore,
                              goal=goal,
                              nsMap=nsMap)
        MapDLPtoNetwork(network,g)
        factualTokens=generateTokenSet(g)
        start = time.time()  
        network.feedFactsToAdd(factualTokens)
        sTime = time.time() - start
        if sTime > 1:
            sTimeStr = "%s seconds"%sTime
        else:
            sTime = sTime * 1000
            sTimeStr = "%s milli seconds"%sTime
        print "Calculated closure in %s "%sTimeStr
        print network
        builder,proof=GenerateProof(network,goal)
        pGraph=Graph()
        builder.serialize(proof,pGraph)
        #print pGraph.serialize(format='n3')
#        for l in builder.trace:
#            print l

    def testProofWitch(self,
                  proof_viz="witches-pf",
                  network_viz='witches_network',
                  goal=(WITCH.GIRL,RDF.type,WITCH.WITCH)):
        ruleStore=self.createRuleStore('witch.n3')
        ruleStore._finalize()
        rs=Ruleset(n3StoreSrc=ruleStore.rules,nsMapping=self.nsMapping)
        network = ReteNetwork(ruleStore,
                              dontFinalize=True,
                              goal=goal,
                              nsMap=self.nsMapping)
        #renderNetwork(network,nsMap=dict(self.nsMapping)).write_graphviz('%s.dot'%network_viz)
        start = time.time()  
        factualTokens=generateTokenSet(Graph().parse('witch.n3',format='n3'))
        self.assertEqual(len(factualTokens),3)
        network.feedFactsToAdd(factualTokens)
        sTime = time.time() - start
        if sTime > 1:
            sTimeStr = "%s seconds"%sTime
        else:
            sTime = sTime * 1000
            sTimeStr = "%s milli seconds"%sTime
        print "Time to calculate closure on working memory: ",sTimeStr        
        print network
        self.failUnless(goal in network.inferredFacts,
                     "Didn't infer %s"%repr(goal))
        builder,proof=GenerateProof(network,goal)
        #builder.renderProof(proof).write_graphviz('%s.dot'%proof_viz)

    def testProofDan(self,proof_src='dan_home.n3',goal=(DAN.dan,DAN.homeRegion,DAN.Texas)):
        ruleStore=self.createRuleStore('dan_home.n3')
        ruleStore._finalize()
        rs=Ruleset(n3StoreSrc=ruleStore.rules,nsMapping=self.nsMapping)
        network = ReteNetwork(ruleStore,
                              dontFinalize=True,
                              goal=goal,
                              nsMap=self.nsMapping)
        start = time.time()  
        factualTokens=generateTokenSet(Graph().parse(proof_src,format='n3'))
        self.assertEqual(len(factualTokens),2,repr([buildUniTerm(i.asTuple(),network.nsMap) for i in factualTokens]))
        network.feedFactsToAdd(factualTokens)
        sTime = time.time() - start
        if sTime > 1:
            sTimeStr = "%s seconds"%sTime
        else:
            sTime = sTime * 1000
            sTimeStr = "%s milli seconds"%sTime
        print "Time to calculate closure on working memory: ",sTimeStr        
        print network
        self.failUnless(goal in network.inferredFacts,
                     "Didn't infer %s"%repr(goal))
        builder,proof=GenerateProof(network,goal)
        
def runTests(profile=False):
    suite = unittest.makeSuite(TestProof)
    if profile:
        #from profile import Profile
        from hotshot import Profile, stats
        p = Profile('fuxi.profile')
        #p = Profile()
        p.runcall(unittest.TextTestRunner(verbosity=5).run,suite)
        p.close()    
        s = stats.load('fuxi.profile')
#        s=p.create_stats()
        s.strip_dirs()
        s.sort_stats('time','cumulative','pcalls')
        s.print_stats(.1)
        s.print_callers(.05)
        s.print_callees(.05)
    else:
        unittest.TextTestRunner(verbosity=5).run(suite)
                
if __name__ == '__main__':
    runTests(profile=False)