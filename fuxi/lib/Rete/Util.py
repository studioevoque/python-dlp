"""
Utility functions for a Boost Graph Library (BGL) DiGraph via the BGL Python Bindings

This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 2.5 License.
To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-sa/2.5/ 
or send a letter to Creative Commons, 543 Howard Street, 5th Floor, San Francisco, California, 94105, USA.
"""
from FuXi.Rete.AlphaNode import AlphaNode

try:
    import boost.graph as bgl
except:
    #Don't have BGL Python library installed
    pass
from rdflib.Graph import Graph
from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib import BNode, Namespace
from sets import Set

LOG = Namespace("http://www.w3.org/2000/10/swap/log#")

def xcombine(*seqin):
    '''
    http://aspn.activestate.com/ASPN/Cookbook/Python/Recipe/302478
    returns a generator which returns combinations of argument sequences
    for example xcombine((1,2),(3,4)) returns a generator; calling the next()
    method on the generator will return [1,3], [1,4], [2,3], [2,4] and
    StopIteration exception.  This will not create the whole list of 
    combinations in memory at once.
    '''
    def rloop(seqin,comb):
        '''recursive looping function'''
        if seqin:                   # any more sequences to process?
            for item in seqin[0]:
                newcomb=comb+[item]     # add next item to current combination
                # call rloop w/ remaining seqs, newcomb
                for item in rloop(seqin[1:],newcomb):   
                    yield item          # seqs and newcomb
        else:                           # processing last sequence
            yield comb                  # comb finished, add to list
    return rloop(seqin,[])

def permu(xs):
    """
    http://aspn.activestate.com/ASPN/Cookbook/Python/Recipe/496819
    "A recursive function to get permutation of a list"
    
    >>> print list(permu([1,2,3]))
    [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]]
     
    """
    if len(xs) <= 1:
        yield xs
    else:
        for i in range(len(xs)):
            for p in permu(xs[:i] + xs[i + 1:]):
                yield [xs[i]] + p

def generateTokenSet(graph,debugTriples=[],skipImplies=True):
    """
    Takes an rdflib graph and generates a corresponding Set of ReteTokens
    Note implication statements are excluded from the realm of facts by default
    """
    print debugTriples
    from FuXi.Rete import ReteToken
    rt = Set()    
    for s,p,o in graph:
        if not skipImplies or p != LOG.implies:
            #print s,p,o             
            debug = (s,p,o) in debugTriples
            rt.add(ReteToken((s,p,o),debug))
    return rt

def generateBGLNode(node,bglGraph,vertexMaps,namespace_manager,identifier,edgeMaps = {}):
    from FuXi.Rete import ReteNetwork,BetaNode,BuiltInAlphaNode,AlphaNode
    from BetaNode import LEFT_MEMORY, RIGHT_MEMORY, LEFT_UNLINKING
    vertex = bglGraph.add_vertex()
    labelMap   = vertexMaps.get('label',bglGraph.vertex_property_map('string'))        
    shapeMap   = vertexMaps.get('shape',bglGraph.vertex_property_map('string'))
    #sizeMap   = vertexMaps.get('size',bglGraph.vertex_property_map('string'))
    rootMap    = vertexMaps.get('root',bglGraph.vertex_property_map('string'))
    outlineMap = vertexMaps.get('peripheries',bglGraph.vertex_property_map('string'))
    idMap      = vertexMaps.get('ids',bglGraph.vertex_property_map('string'))
    #widthMap   = vertexMaps.get('width',bglGraph.vertex_property_map('string'))
    idMap[vertex] = identifier
    shapeMap[vertex] = 'circle'
    #sizeMap[vertex] = '10'
    if isinstance(node,ReteNetwork):     
        rootMap[vertex] = 'true'
        outlineMap[vertex] = '3'
    elif isinstance(node,BetaNode) and not node.consequent:     
        outlineMap[vertex] = '1'
        if node.aPassThru:
            labelMap[vertex] = str("Pass-thru Beta node\\n")
        elif node.commonVariables:
            labelMap[vertex] = str("Beta node\\n(%s)"%(','.join(["?%s"%i for i in node.commonVariables])))
        else:
            labelMap[vertex] = "Beta node"

        leftMemNode = bglGraph.add_vertex() 
        rightMemNode = bglGraph.add_vertex() 
        edge1 = bglGraph.add_edge(vertex,leftMemNode)
        edge2 = bglGraph.add_edge(vertex,rightMemNode)
        
        for pos,memory,bglNode in [ (LEFT_MEMORY,node.memories[LEFT_MEMORY],leftMemNode),
                                (RIGHT_MEMORY,node.memories[RIGHT_MEMORY],rightMemNode)]:            
            if memory:
                labelMap[bglNode] = '\\n'.join([repr(token) for token in memory])
            shapeMap[bglNode] = 'plaintext'
            idMap[bglNode] = str(int(identifier) * 200 + pos)

        if isinstance(node,BuiltInAlphaNode):
            raise NotImplemented("N3 builtins not supported") 
            builtInsVertex = bglGraph.add_vertex() 
            edge = bglGraph.add_edge(builtInsVertex,vertex)
            funcList = node.functionIndex and reduce(lambda x,y: x+y,node.functionIndex.values()) or []
            labelMap[builtInsVertex] = '\\n'.join([repr(builtIn) for builtIn in funcList + node.filters])
            shapeMap[builtInsVertex] = 'plaintext'

    elif isinstance(node,BetaNode) and node.consequent:     
        #rootMap[vertex] = 'true'
        outlineMap[vertex] = '2'        
        stmts = []
        for s,p,o in node.consequent:
            stmts.append(' '.join([str(namespace_manager.normalizeUri(s)),
              str(namespace_manager.normalizeUri(p)),
              str(namespace_manager.normalizeUri(o))]))
              
        rhsVertex = bglGraph.add_vertex() 
        edge = bglGraph.add_edge(vertex,rhsVertex)
        labelMap[rhsVertex] = '\\n'.join(stmts)
        shapeMap[rhsVertex] = 'plaintext'
        idMap[rhsVertex]    = str(BNode())
        if node.commonVariables:
            labelMap[vertex] = str("Terminal node\\n(%s)"%(','.join(["?%s"%i for i in node.commonVariables])))
        else:
            labelMap[vertex] = "Terminal node"

        leftMemNode = bglGraph.add_vertex() 
        rightMemNode = bglGraph.add_vertex() 
        edge1 = bglGraph.add_edge(vertex,leftMemNode)
        edge2 = bglGraph.add_edge(vertex,rightMemNode)
        
        for pos,memory,bglNode in [ (LEFT_MEMORY,node.memories[LEFT_MEMORY],leftMemNode),
                                (RIGHT_MEMORY,node.memories[RIGHT_MEMORY],rightMemNode)]:            
            if memory:
                labelMap[bglNode] = '\\n'.join([repr(token) for token in memory])
            shapeMap[bglNode] = 'plaintext'
            idMap[bglNode] = str(int(identifier) * 200 + pos)

        if isinstance(node,BuiltInAlphaNode):
            raise NotImplemented("N3 builtins not supported") 
            builtInsVertex = bglGraph.add_vertex() 
            edge = bglGraph.add_edge(builtInsVertex,vertex)
            funcList = node.functionIndex and reduce(lambda x,y: x+y,node.functionIndex.values()) or []
            labelMap[builtInsVertex] = '\\n'.join([repr(builtIn) for builtIn in funcList + node.filters])
            shapeMap[builtInsVertex] = 'plaintext'
        
    elif isinstance(node,BuiltInAlphaNode):
        outlineMap[vertex] = '1'
        shapeMap[vertex] = 'plaintext'
        labelMap[vertex] = '..Builtin Source..'
        
    elif isinstance(node,AlphaNode):
        outlineMap[vertex] = '1'
        shapeMap[vertex] = 'plaintext'
#        widthMap[vertex] = '50em'
        labelMap[vertex] = ' '.join([str(namespace_manager.normalizeUri(i)) for i in node.triplePattern])    


    vertexMaps['ids'] = idMap
    vertexMaps['label'] = labelMap
    vertexMaps['shape'] = shapeMap
#    vertexMaps['width'] = widthMap
    vertexMaps['root'] = rootMap
    vertexMaps['peripheries'] = outlineMap
    #vertexMaps['size'] = sizeMap[vertex]
    bglGraph.vertex_properties['node_id'] = idMap
    bglGraph.vertex_properties['label'] = labelMap
    bglGraph.vertex_properties['shape'] = shapeMap
#    bglGraph.vertex_properties['width'] = widthMap
    bglGraph.vertex_properties['root'] = rootMap
    bglGraph.vertex_properties['peripheries'] = outlineMap
    return vertex

def renderNetwork(network,nsMap = {}):
    """
    Takes an instance of a compiled ReteNetwork and a namespace mapping (for constructing QNames
    for rule pattern terms) and returns a BGL Digraph instance representing the Rete network
    #(from which GraphViz diagrams can be generated)
    """
    from FuXi.Rete import BuiltInAlphaNode
    from BetaNode import LEFT_MEMORY, RIGHT_MEMORY, LEFT_UNLINKING
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
    for node in network.nodes.values():
        if not node in visitedNodes and not isinstance(node,BuiltInAlphaNode):
            idx += 1
            visitedNodes[node] = generateBGLNode(node,bglGraph,vertexMaps,namespace_manager,str(idx),edgeMaps)
    nodeIdxs = {}                        
    for node in network.nodes.values():
        for mem in node.descendentMemory:
            if not mem:
                continue
            bNode = mem.successor
        #for bNode in node.descendentBetaNodes:
            for otherNode in [bNode.leftNode,bNode.rightNode]:
                if node == otherNode and (node,otherNode) not in edges:
                    if isinstance(node,BuiltInAlphaNode):
                        continue
                    for i in [node,bNode]:
                        if i not in visitedNodes:
                            idx += 1
                            nodeIdxs[i] = idx 
                            visitedNodes[i] = generateBGLNode(i,bglGraph,vertexMaps,namespace_manager,str(idx))
                            
                    edge = bglGraph.add_edge(visitedNodes[node],visitedNodes[bNode])
                    edges.append((node,bNode))
                    if node in bNode.leftUnlinkedNodes:
                        labelMap         = edgeMaps.get('label',bglGraph.edge_property_map('string'))
                        colorMap         = edgeMaps.get('color',bglGraph.edge_property_map('string'))
                        labelMap[edge]   = "left re-linked"
                        colorMap[edge]   = "red"
                        idMap            = edgeMaps.get('ids',bglGraph.edge_property_map('string'))
                        idMap[edge]      = str(visitedNodes[node]) + str(visitedNodes[bNode]) + 'edge'                        
                        edgeMaps['ids']   = idMap
                        edgeMaps['color'] = colorMap
                        edgeMaps['label'] = labelMap
                        bglGraph.edge_properties['label'] = labelMap
                    
    return bglGraph

def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()    