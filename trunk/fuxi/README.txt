## Introduction (Why the Weird Name?) ##

FuXi (pronounced foo-shee) is a forward-chaining production system for Notation 3 Description Logic Programming [1].
It is implemented as a companion to RDFLib [2] – which it requires for its various RDF processing.  It is named 
after the first mythical sovereign of ancient china who supposedly, 'looked upward and contemplated the images in 
the heavens, and looked downward and contemplated the occurrences on earth.'.  
 
Originally, it was an idea to express the underlying constructs of the Yi Jing / I Ching in Description & 
First Order Logic in order to reason over them. 

The more practical motivation for developing FuXi (besides the software dependency difficulties associated with
 its predecessor – Pychinko) was the reality (in my opinion) that Tableux-based reasoners will never be able to
 outperform production systems for the subset of Description Logics that can be implemented in production systems. 
This subset (which is probably sufficient for the most common usage of DL) is often referred to as 
Description Logics or pD* (see Horst Herman J's paper [3] on this subset)
 
## Background of RETE and RETE/UL Algorithms ##

It relies on Charles Forgy's Rete algorithm [4] for the many pattern/many object match problem.  It also
 implements algorithms outlined in the PhD thesis [5] (1995) of Robert Doorenbos:

    Production Matching for Large Learning Systems.

Robert's thesis describes a modification of the original Rete algorithm that (amongst other things) limits 
the fact syntax (referred to as Working Memory Elements) to 3-item tuples (which corresponds quite nicely with
 the RDF abstract syntax).  The thesis also describes methods for using hash tables to improve efficiency of 
alpha nodes and beta nodes.  

An introductory description from the above these:

Rete (usually pronounced either "REET" or "REE-tee," from the Latin word for "network") deals with a production
 memory (PM) and a working memory (WM). Each of these may change gradually over time. The working memory is a
 set of items which (in most systems) represent facts about the system's current situation - the state of the
 external world and/or the internal problem-solving state of the system itself. Each item in WM is called a
 working memory element,or a WME.

The production memory is a set of productions (i.e., rules). A production is specified as a set of conditions,
 collectively called the left-hand side (LHS), and a set of actions, collectively called the right-hand side (RHS).

## Roadmap & Limitations ##

FuXi currently implements production capabilities for a limited subset of Notation 3.  In particular built-ins
 are not implemented as they have a significant impact on the efficiency of a RETE network (which was really 
only intended for pattern matching).  Robert's thesis includes algorithms / heuristics for implementing support for:

- Negation 
- Non-equality tests (read: built-in support)
- Live addition/removal of rules
- Support for removal of triples / WMEs

The long term plan is to roll these into the current implementation

## Python Idioms ##

Like RDFLib, FuXi is very idiomatic and uses Python hash / set / list mechanism to maximize the matching efficiency
 of the network.  The extent of the efficiency has not been fully explored and there is much more that can be done
 to improve the already impressive performance.

## Usage ##

FuXi is meant to work with a RuleStore, an initial working memory (the initial RDF graph), and a closure graph
 (where the inferred triples are added).  The RuleStore is a specialized RDFLib Store into which an N3 document
 is parsed.  Its main purpose is to maintain the order of patterns in N3 formulae which can lose their order in
 a regular RDF store since RDF doesn't mandate a specific order to triples in a graph.  For example:

            from FuXi.Rete.Util import generateTokenSet
            from FuXi.Rete import *
            from rdflib.Graph import Graph,ReadOnlyGraphAggregate
            from rdflib import plugin
            from FuXi.Rete.RuleStore import N3RuleStore
        	store = plugin.get('IOMemory',Store)()
            store.open('')
            ruleGraph = Graph(N3RuleStore())
            ruleGraph.parse(open('some-rule-file.n3'),format='n3')             
            factGraph = Graph(store)
            factGraph.parse(open('fact-file'),format='..')
            deltaGraph = Graph(store)            
            network = ReteNetwork(ruleStore,
                                  initialWorkingMemory=generateTokenSet(factGraph),
                                  inferredTarget = deltaGraph)            
            for s,p,o in network.closureGraph(factGraph):
                .. do something with triple ..


## Other capabilities ##

In addition to implementing the compilation (and evaluation) of a RETE network from an N3 document, 
FuXi can also export the compiled network into a diagram using Boost Graph Library (BGL) Python Bindings [6]:


            bglGraph = renderNetwork(reteNetwork,nsMap=nsMap)
            bglGraph.write_graphviz('rules.dot')

nsMap is a namespace mapping (for constructing Qnames for rule pattern terms) from prefixes to URI's.

Various BGL-Graph algorithms can then be applied to bglGraph:

    * Breadth First Search
    * Depth First Search
    * Uniform Cost Search

As well as heuristics:

    * Dijkstra's Shortest Paths
    * Bellman-Ford Shortest Paths
    * Johnson's All-Pairs Shortest Paths
    * Kruskal's Minimum Spanning Tree
    * Prim's Minimum Spanning Tree
    * Connected Components
    * Strongly Connected Components
    * Dynamic Connected Components (using Disjoint Sets)
    * Topological Sort
    * Transpose
    * Reverse Cuthill Mckee Ordering
    * Smallest Last Vertex Ordering
    * Sequential Vertex Coloring

[1] http://logic.aifb.uni-karlsruhe.de/
[2] http://rdflib.net
[3] http://www.websemanticsjournal.org/ps/pub/2005-15
[4] http://citeseer.ist.psu.edu/context/6275/0
[5] http://reports-archive.adm.cs.cmu.edu/anon/1995/CMU-CS-95-113.pdf
[6] http://www.osl.iu.edu/~dgregor/bgl-python/

Chimezie Ogbuji
