#!/usr/bin/env python
from pprint import pprint
from sets import Set
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef,Literal,Variable
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
import unittest
import boost.graph as bgl

RDFLIB_CONNECTION=''
RDFLIB_STORE='IOMemory'

FOAF_NS = Namespace('http://xmlns.com/foaf/0.1/')

import getopt, sys

def generateBGLNode((node,graph),bglGraph,vertexMaps,namespace_manager,identifier,outline=False):
    vertex = bglGraph.add_vertex()
    labelMap   = vertexMaps.get('label',bglGraph.vertex_property_map('string'))        
    shapeMap   = vertexMaps.get('shape',bglGraph.vertex_property_map('string'))
    rootMap    = vertexMaps.get('root',bglGraph.vertex_property_map('string'))
    outlineMap = vertexMaps.get('peripheries',bglGraph.vertex_property_map('string'))
    idMap      = vertexMaps.get('ids',bglGraph.vertex_property_map('string'))
    if outline:
        outlineMap[vertex] = '3'
    #widthMap   = vertexMaps.get('width',bglGraph.vertex_property_map('string'))
    idMap[vertex] = identifier
    shapeMap[vertex] = 'circle'
    #        widthMap[vertex] = '50em'
    #shapeMap[rhsVertex] = 'plaintext'
    #rootMap[vertex] = 'true'
    #outlineMap[vertex] = '3'
    for s,p,label in graph.triples((node,FOAF_NS.name,None)):
        labelMap[vertex] = str(label)

    vertexMaps['ids'] = idMap
    vertexMaps['label'] = labelMap
    vertexMaps['shape'] = shapeMap
#    vertexMaps['width'] = widthMap
    vertexMaps['root'] = rootMap
    vertexMaps['peripheries'] = outlineMap
    bglGraph.vertex_properties['node_id'] = idMap
    bglGraph.vertex_properties['label'] = labelMap
    bglGraph.vertex_properties['shape'] = shapeMap
#    bglGraph.vertex_properties['width'] = widthMap
    bglGraph.vertex_properties['root'] = rootMap
    bglGraph.vertex_properties['peripheries'] = outlineMap
    return vertex

def renderFOAFNetwork(graph,nicks,nsMap = {}):
    try:    
        bglGraph = bgl.Digraph()
    except:
        raise NotImplementedError("Boost Graph Library & Python bindings not installed.  See: see: http://www.osl.iu.edu/~dgregor/bgl-python/")
    namespace_manager = NamespaceManager(Graph())
    vertexMaps   = {}
    edgeMaps     = {}
    for prefix,uri in nsMap.items():
        namespace_manager.bind(prefix, uri, override=False)

    visitedNodes = {}
    edges = []
    idx = 0
    edgeIDX = 0
    excludedPeople = Set()
    #collect exluded people
    print nicks
    for s,p,o in graph.triples((None,FOAF_NS.knows,None)):
        for node in [s,o]:
            if not node in visitedNodes:
                included = False
                _nicks = []
                for s2,p2,nick in graph.triples((node,FOAF_NS.nick,None)):                    
                    _nicks.append(str(nick))
                    if str(nick) in nicks:
                        included = True
                        break
                if not included:
                    print "exluding ", node
                    print "\t",_nicks, nicks
                    excludedPeople.add(node)
    
    for s,p,o in graph.triples((None,FOAF_NS.knows,None)):
        if s in excludedPeople:
            print "skipping ", s
            continue
        for node in [s,o]:
            if not node in visitedNodes:
                idx += 1
                visitedNodes[node] = generateBGLNode((node,graph),bglGraph,vertexMaps,namespace_manager,str(idx),node not in excludedPeople)
        if (s,o) not in edges:
            edgeIDX += 1
            edge             = bglGraph.add_edge(visitedNodes[s],visitedNodes[o])
            labelMap         = edgeMaps.get('label',bglGraph.edge_property_map('string'))
            labelMap[edge]   = "foaf:knows"
            idMap            = edgeMaps.get('ids',bglGraph.edge_property_map('string'))
            idMap[edge]      = str(edgeIDX)
            
            edgeMaps['ids']   = idMap
            edgeMaps['label'] = labelMap
            bglGraph.edge_properties['label'] = labelMap
            bglGraph.edge_properties['ids']   = idMap
            edges.append((s,o))
    return bglGraph


def usage():
    print "FOAFVisualize.py [--help] [--stdin] [--nicks=<.. foaf nicks ..>] [--output=<.. output.dot ..>] [--input-format=<'n3' or 'xml'>] [--ns=prefix=namespaceUri] --input=<facts1.n3,facts2.n3,..>"

def main():
    try:
        opts, args = getopt.getopt(sys.argv[1:], "", ["nicks=","output=","ns=","input=","stdin","help","input-format="])
    except getopt.GetoptError, e:
        # print help information and exit:
        print e
        usage()
        sys.exit(2)

    factGraphs = []
    factFormat = 'xml'
    useRuleFacts = False
    nsBinds = {
        'rdf' : RDF.RDFNS,
        'rdfs': RDFS.RDFSNS,
        'owl' : "http://www.w3.org/2002/07/owl#",       
        'dc'  : "http://purl.org/dc/elements/1.1/",
        'foaf': "http://xmlns.com/foaf/0.1/",
        'wot' : "http://xmlns.com/wot/0.1/"        
    }
    outMode = None
    stdIn = False
    gVizOut = 'output.dot'
    nicks=[]
    if not opts:
        usage()
        sys.exit()        
    for o, a in opts:
        if o == '--input-format':
            factFormat = a
        elif o == '--nicks':
            nicks = a.split(',')
        elif o == '--stdin':
            stdIn = True
        elif o == '--output':
            gVizOut = a
        elif o == '--ns':            
            pref,nsUri = a.split('=')
            nsBinds[pref]=nsUri
        elif o == "--input":
            factGraphs = a.split(',')
        elif o == "--help":
            usage()
            sys.exit()
        
    store = plugin.get(RDFLIB_STORE,Store)()        
    store.open(RDFLIB_CONNECTION)
    namespace_manager = NamespaceManager(Graph())
    for prefix,uri in nsBinds.items():
        namespace_manager.bind(prefix, uri, override=False)    
    factGraph = Graph(store) 
    factGraph.namespace_manager = namespace_manager
    if factGraphs:
        for fileN in factGraphs:
            factGraph.parse(open(fileN),format=factFormat)
    if stdIn:
        factGraph.parse(sys.stdin,format=factFormat)

    renderFOAFNetwork(factGraph,nicks,nsMap=nsBinds).write_graphviz(gVizOut)
    store.rollback()

if __name__ == "__main__":
    main()
