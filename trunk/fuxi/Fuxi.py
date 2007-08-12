#!/usr/bin/env python
from pprint import pprint
from sets import Set
from FuXi.Rete import ReteNetwork
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.BetaNode import PartialInstanciation, LEFT_MEMORY, RIGHT_MEMORY
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import renderNetwork,generateTokenSet, xcombine
from FuXi.DLP import MapDLPtoNetwork
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef,Literal,Variable
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
import unittest, time

RDFLIB_CONNECTION=''
RDFLIB_STORE='IOMemory'

import getopt, sys

def usage():
    print "Fuxi.py [--help] [--stdin] [--ruleFacts] [--output=<'conflict' or 'n3' or 'xml'>] [--input-format=<'n3' or 'xml'>] [--ns=prefix=namespaceUri] [--graphviz-out=<file.out>] --facts=<facts1.n3,facts2.n3,..> --rules=<rule1.n3,rule2.n3>"
    print "Output:"
    print "\tThe --output option determines whether to serialize the inferred triples to STDOUT or to print a summary of the"
    print "\tconflict set (from the RETE network)"
    print "Rule Facts:"
    print "\tThe --ruleFacts switch determines whether or not to attempt to parse initial facts from the rule graph"
    print "RETE network diagram:"
    print "\tThe graphviz-out option is a filename to write a graphviz diagram of the RETE network to"
    print "Input format"
    print "\tThe --input-format option determines the format of the RDF document(s) specified by --facts"
    print "Description Logic Programming"
    print "\tThe --dlp switch turns on DLP reasoning.  In this mode, the input document is considered a Description Horn Logic ontology, and a compiled ruleset is mapped into a Network"
    print "Namespace bindings:"
    print "\tThe --ns option adds a prefix to namespace binding and is used by both the generated RETE network diagram and the serialization (if specified by --out)"

def main():
    try:
        opts, args = getopt.getopt(sys.argv[1:], "", ["optimize",
                                                      "output=",
                                                      "ns=",
                                                      "dlp",
                                                      "facts=", 
                                                      "rules=",
                                                      "stdin",
                                                      "help",
                                                      "ruleFacts",
                                                      "graphviz-out=",
                                                      "input-format=",
                                                      "conflict"])
    except getopt.GetoptError, e:
        # print help information and exit:
        print e
        usage()
        sys.exit(2)

    factGraphs = []
    ruleGraphs = []
    factFormat = 'xml'
    useRuleFacts = False
    gVizOut = None
    nsBinds = {}
    outMode = 'n3'
    optimize = False
    stdIn = False
    dlp = False
    if not opts:
        usage()
        sys.exit()        
    for o, a in opts:
        if o == '--input-format':
            factFormat = a
        elif o == '--stdin':
            stdIn = True
        elif o == '--optimize':
            optimize = True            
        elif o == '--output':
            outMode = a
        elif o == '--ns':            
            pref,nsUri = a.split('=')
            nsBinds[pref]=nsUri
        elif o == '--graphviz-out':
            gVizOut = a
        elif o == "--facts":
            factGraphs = a.split(',')
        elif o == "--help":
            usage()
            sys.exit()
        elif o == '--dlp':
            dlp = True
        elif o == "--rules":
            ruleGraphs = a.split(',')
        elif o == '--ruleFacts':
            useRuleFacts = True

    store = plugin.get(RDFLIB_STORE,Store)()        
    store.open(RDFLIB_CONNECTION)
    
    namespace_manager = NamespaceManager(Graph())
    for prefix,uri in nsBinds.items():
        namespace_manager.bind(prefix, uri, override=False)    
    ruleStore=N3RuleStore()
    ruleGraph = Graph(ruleStore)            
    closureDeltaGraph = Graph(store,namespace_manager=namespace_manager)
    factGraph = Graph(store) 
    for fileN in ruleGraphs:
        ruleGraph.parse(open(fileN),format='n3')
        if useRuleFacts:
            factGraph.parse(open(fileN),format='n3')
    if optimize:
        ruleStore.optimizeRules()
        sys.exit(1)
    if factGraphs:
        for fileN in factGraphs:
            factGraph.parse(open(fileN),format=factFormat)
    if stdIn:
        factGraph.parse(sys.stdin,format=factFormat)
    workingMemory = generateTokenSet(factGraph)
    network = ReteNetwork(ruleStore,
                          inferredTarget = closureDeltaGraph,
                          graphVizOutFile = gVizOut,
                          nsMap = nsBinds)
    if dlp:
        MapDLPtoNetwork(network,factGraph)
    start = time.time()  
    network.feedFactsToAdd(workingMemory)
    sTime = time.time() - start
    if sTime > 1:
        sTimeStr = "%s seconds"%sTime
    else:
        sTime = sTime * 1000
        sTimeStr = "%s milli seconds"%sTime
    print "Time to calculate closure on working memory: ",sTimeStr

    if outMode in ['n3','xml']:        
        #print network.inferredFacts.serialize(destination=None, format=outMode, base=None)
        print network.closureGraph(factGraph).serialize(destination=None, format=outMode, base=None)
    elif outMode == 'conflict':
        tNodeOrder = [tNode for tNode in network.terminalNodes if network.instanciations[tNode]]
        tNodeOrder.sort(key=lambda x:network.instanciations[x],reverse=True)
        for termNode in tNodeOrder:
            lhsF,rhsF = termNode.ruleFormulae
            print termNode
            #print "\t %s => %s"%(lhsF,rhsF)
            print "\t", rhsF
            print "\t\t%s instanciations"%network.instanciations[termNode]
    print >> sys.stderr, repr(network)
    store.rollback()

if __name__ == "__main__":
    main()
