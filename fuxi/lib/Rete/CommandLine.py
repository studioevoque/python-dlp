#!/usr/bin/env python
from pprint import pprint
from sets import Set
from FuXi.Rete import ReteNetwork
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

import getopt, sys

def usage():
    print """USAGE: Fuxi [options] factFile1 factFile2 ...
Options:
  --closure                  If present, the inferred triples are serialized 
                             along with the original triples if asked for. Otherwise
                             (the default behavior), only the inferred triples
                             are serialized
                             
  --output=OUT               Determines whether to serialize the inferred triples
                             to STDOUT using the specified RDF syntax ('xml','pretty-xml',
                             'nt','turtle',or 'n3') or to print a summary of the conflict set 
                             (from the RETE network) if the value of this option is
                             'conflict'
  --help
  --input-format=<FORMAT>    Determines the format of the RDF document(s) which
                             serve as the initial facts for the RETE network.
                             One of 'n3','trix', 'nt', or 'rdfa'
                             
  --optimize                 Suggest inefficiencies in the ruleset and exit
                     
  --stdin                    Parse STDIN as an RDF graph to contribute to the
                             initial facts for the RETE network using the 
                             specified format
                             
  --ns=PREFIX=NSURI          Register a namespace binding (QName prefix to a 
                             base URI).  This can be used more than once
                             
  --graphviz-out=<FILE>      A filename to write a graphviz diagram of the RETE
                             network to
  
  --rules=FILE1,FILE2,..     The Notation 3 documents to use as rulesets for the
                             RETE network
                             
  ---ruleFacts               Determines whether or not to attempt to parse 
                             initial facts from the rule graph.  Default by default"""    
def main():
    try:
        opts, args = getopt.getopt(sys.argv[1:], "", ["optimize","output=","ns=","facts=", "rules=","stdin","help","ruleFacts","graphviz-out=","input-format=","closure"])
    except getopt.GetoptError, e:
        # print help information and exit:
        print e
        usage()
        sys.exit(2)

    factGraphs = args
    ruleGraphs = []
    factFormat = 'xml'
    useRuleFacts = False
    gVizOut = None
    nsBinds = {}
    outMode = 'n3'
    optimize = False
    stdIn = False
    closure = False
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
        elif o == "--help":
            usage()
            sys.exit()
        elif o == "--rules":
            ruleGraphs = a.split(',')
        elif o == '--ruleFacts':
            useRuleFacts = True
        elif o == '--closure':
            closure = True
    store = plugin.get(RDFLIB_STORE,Store)()        
    store.open(RDFLIB_CONNECTION)
    
    namespace_manager = NamespaceManager(Graph())
    for prefix,uri in nsBinds.items():
        namespace_manager.bind(prefix, uri, override=False)    
    ruleStore=N3RuleStore()
    ruleGraph = Graph(ruleStore)            
    closureDeltaGraph = Graph(store)
    closureDeltaGraph.namespace_manager = namespace_manager
    factGraph = Graph(store) 
    factGraph.namespace_manager = namespace_manager
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
                          initialWorkingMemory=workingMemory,
                          inferredTarget = closureDeltaGraph,
                          graphVizOutFile = gVizOut,
                          nsMap = nsBinds)
    if outMode == 'conflict':
        tNodeOrder = [tNode for tNode in network.terminalNodes if network.instanciations[tNode]]
        tNodeOrder.sort(key=lambda x:network.instanciations[x],reverse=True)
        for termNode in tNodeOrder:
            lhsF,rhsF = termNode.ruleFormulae
            print termNode
            #print "\t %s => %s"%(lhsF,rhsF)
            print "\t", rhsF
            print "\t\t%s instanciations"%network.instanciations[termNode]
    else:        
        if closure:
            cGraph = network.closureGraph(factGraph)
            cGraph.namespace_manager = namespace_manager
            for g in cGraph.graphs:
                g.namespace_manager = namespace_manager
            print cGraph.serialize(destination=None, format=outMode, base=None)
        else:
            print network.inferredFacts.serialize(destination=None, format=outMode, base=None)            
    print >> sys.stderr, repr(network)
    store.rollback()

if __name__ == "__main__":
    main()
