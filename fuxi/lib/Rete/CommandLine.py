#!/usr/bin/env python
from pprint import pprint
from sets import Set
from FuXi.Rete import ReteNetwork
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.BetaNode import PartialInstanciation, LEFT_MEMORY, RIGHT_MEMORY
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import renderNetwork,generateTokenSet, xcombine
from FuXi.DLP import MapDLPtoNetwork, non_DHL_OWL_Semantics
from FuXi.Syntax.InfixOWL import *
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef,Literal,Variable
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
import unittest, time, warnings

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
  --man-owl                  If present, either the closure (or just the inferred triples) are serialized 
                             using an extension of the manchester OWL syntax
                             with indications for ontology normalization
                             (http://www.cs.man.ac.uk/~rector/papers/rector-modularisation-kcap-2003-distrib.pdf)
  --normalize                Will attempt to determine if the ontology is 'normalized' [Rector, A. 2003]                             
  --help
  --input-format=<FORMAT>    Determines the format of the RDF document(s) which
                             serve as the initial facts for the RETE network.
                             One of 'xml','n3','trix', 'nt', or 'rdfa'.  The default
                             is 'xml'.
                             
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
                             initial facts from the rule graph.  Default by default
                             
   --dlp                     This switch turns on Description Logic Programming 
                             (DLP) inference.  In this mode, the input document 
                             is considered an OWL ontology mostly comprised of
                             Description Horn Logic (DHL) axioms. ontology.  An 
                             additional ruleset is included to capture those 
                             semantics outside DHL but which can be expressed in
                             definite Datalog Logic Programming.  The DHL-compiled 
                             ruleset and the extensions are mapped into a RETE-UL 
                             Network for evaluateion."""    
def main():
    try:
        opts, args = getopt.getopt(sys.argv[1:], "", ["optimize",
                                                      "output=",
                                                      "ns=",
                                                      "facts=", 
                                                      "rules=",
                                                      "normalize",
                                                      "man-owl",
                                                      "dlp",
                                                      "stdin",
                                                      "help",
                                                      "ruleFacts",
                                                      "graphviz-out=",
                                                      "input-format=",
                                                      "closure"])
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
    dlp = False
    manOWL = False
    normalize=False
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
        elif o == '--normalize':
            normalize = True            
        elif o == '--output':
            outMode = a
        elif o == '--ns':            
            pref,nsUri = a.split('=')
            nsBinds[pref]=nsUri
        elif o == '--graphviz-out':
            gVizOut = a
        elif o == '--man-owl':
            manOWL = True
        elif o == "--help":
            usage()
            sys.exit()
        elif o == '--dlp':
            dlp = True
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
        ruleGraph.parse(fileN,format='n3')
        if useRuleFacts:
            factGraph.parse(fileN,format='n3')
    if optimize:
        ruleStore.optimizeRules()
        sys.exit(1)
    if factGraphs:
        for fileN in factGraphs:
            factGraph.parse(fileN,format=factFormat)
    if stdIn:
        factGraph.parse(sys.stdin,format=factFormat)
    workingMemory = generateTokenSet(factGraph)
    if dlp:
        ruleGraph.parse(StringIO(non_DHL_OWL_Semantics),format='n3')
        network = ReteNetwork(ruleStore,
                              inferredTarget = closureDeltaGraph,
                              graphVizOutFile = gVizOut,
                              nsMap = nsBinds)
        start = time.time()  
        MapDLPtoNetwork(network,factGraph)
        sTime = time.time() - start
        if sTime > 1:
            sTimeStr = "%s seconds"%sTime
        else:
            sTime = sTime * 1000
            sTimeStr = "%s milli seconds"%sTime
        print "Time to map Description Horn Logic axioms to definite Horn clauses and import into network: ",sTimeStr
        print network
    else:
        network = ReteNetwork(ruleStore,
                              inferredTarget = closureDeltaGraph,
                              graphVizOutFile = gVizOut,
                              nsMap = nsBinds)
    
    start = time.time()  
    network.feedFactsToAdd(workingMemory)
    sTime = time.time() - start
    if sTime > 1:
        sTimeStr = "%s seconds"%sTime
    else:
        sTime = sTime * 1000
        sTimeStr = "%s milli seconds"%sTime
    print "Time to calculate closure on working memory: ",sTimeStr
        
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
        if manOWL:
            cGraph = network.closureGraph(factGraph)
            cloneGraph = Graph()
            cloneGraph += cGraph
            cloneGraph.namespace_manager = namespace_manager
            Class.factoryGraph = cloneGraph
            for c in AllClasses(cGraph):#cGraph.subjects(predicate=RDF.type,object=OWL_NS.Class):
                if normalize:
                    if c.isPrimitive():
                        primAnc = [sc for sc in c.subClassOf if sc.isPrimitive()] 
                        if len(primAnc)>1:
                            warnings.warn("Branches of primitive skeleton taxonomy should form trees: %s has %s primitive parents"%(c.qname,len(primAnc)),UserWarning,1)
                        children = [desc for desc in c.subSumpteeIds()]
                        for child in children:
                            for otherChild in [o for o in children if o is not child]:
                                if not otherChild in [c.identifier \
                                                        for c in Class(child).disjointWith]:
                                    warnings.warn("Primitive children (of %s) must be mutually disjoint: %s and %s"%(
                                                                                    c.qname,
                                                                                    Class(child).qname,
                                                                                    Class(otherChild).qname),UserWarning,1)
                if not isinstance(c,BNode):
                    print c.__repr__(True)
        elif closure:
            #FIXME: The code below *should* work
            cGraph = network.closureGraph(factGraph)
            cGraph.namespace_manager = namespace_manager
            print cGraph.serialize(destination=None, format=outMode, base=None)
        else:
            print network.inferredFacts.serialize(destination=None, format=outMode, base=None)
    print >> sys.stderr, repr(network)
    store.rollback()

if __name__ == "__main__":
    main()
