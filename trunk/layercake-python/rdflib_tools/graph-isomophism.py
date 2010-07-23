#!/usr/bin/env python
# encoding: utf-8
"""
graph-isomophism.py

Created by Chimezie Ogbuji on 2010-05-21.
Copyright (c) 2010 __MyCompanyName__. All rights reserved.
"""

import sys
import getopt
from rdflib.Graph import Graph
from rdflib import BNode

class IsomorphicTestableGraph(Graph):
    """
    Ported from http://www.w3.org/2001/sw/DataAccess/proto-tests/tools/rdfdiff.py
     (Sean B Palmer's RDF Graph Isomorphism Tester)
    """
    def __init__(self, **kargs): 
        super(IsomorphicTestableGraph,self).__init__(**kargs)
        self.hash = None
        
    def internal_hash(self):
        """
        This is defined instead of __hash__ to avoid a circular recursion scenario with the Memory
        store for rdflib which requires a hash lookup in order to return a generator of triples
        """ 
        return hash(tuple(sorted(self.hashtriples())))

    def hashtriples(self): 
        for triple in self: 
            g = ((isinstance(t,BNode) and self.vhash(t)) or t for t in triple)
            yield hash(tuple(g))

    def vhash(self, term, done=False): 
        return tuple(sorted(self.vhashtriples(term, done)))

    def vhashtriples(self, term, done): 
        for t in self: 
            if term in t: yield tuple(self.vhashtriple(t, term, done))

    def vhashtriple(self, triple, term, done): 
        for p in xrange(3): 
            if not isinstance(triple[p], BNode): yield triple[p]
            elif done or (triple[p] == term): yield p
            else: yield self.vhash(triple[p], done=True)
      
    def __eq__(self, G): 
        """Graph isomorphism testing."""
        if not isinstance(G, IsomorphicTestableGraph): return False
        elif len(self) != len(G): return False
        elif list.__eq__(list(self),list(G)): return True # @@
        return self.internal_hash() == G.internal_hash()

    def __ne__(self, G): 
       """Negative graph isomorphism testing."""
       return not self.__eq__(G)

if __name__ == "__main__":
    from optparse import OptionParser
    import sys
    op = OptionParser('usage: %prog [--test] runID ccfId1 ccfId2 ccfId3 ... ccfIdN')
    op.add_option('--input-format', 
                  default='xml',
                  dest='inputFormat',
                  metavar='RDF_FORMAT',
                  choices = ['xml', 'trix', 'n3', 'nt', 'rdfa'],
      help = "The format of the RDF documents.  The default is %default")
    # op.add_option('--test', action='store_true',default=False,
    #   help = 'Whether or not to run unit tests')
    (options, args) = op.parse_args()
    
    file1,file2 = args
    graph1 = IsomorphicTestableGraph().parse(file1,format=options.inputFormat)
    graph2 = IsomorphicTestableGraph().parse(file2,format=options.inputFormat)
    print "They are isomorphic to each other? ", graph1 == graph2
    print "Lengths: %s v.s. %s"%(len(graph1),len(graph2))
