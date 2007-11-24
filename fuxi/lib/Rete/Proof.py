"""
Proof Markup Language Construction: Proof Level Concepts (Abstract Syntax)

A set of Python objects which create a PML instance in order to serialize as OWL/RDF

"""
from FuXi.Syntax.InfixOWL import *
from FuXi.Horn.HornRules import Clause, Ruleset
from FuXi.Horn.PositiveConditions import Uniterm, buildUniTerm
from BetaNode import BetaNode, LEFT_MEMORY, RIGHT_MEMORY, PartialInstanciation
from FuXi.Rete.AlphaNode import AlphaNode
from FuXi.Rete.Network import _mulPatternWithSubstitutions
from rdflib.Graph import Graph
from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib import BNode, Namespace
from sets import Set
from pprint import pprint,pformat

PML = Namespace('http://inferenceweb.stanford.edu/2004/07/iw.owl#')
FUXI=URIRef('http://purl.org/net/chimezie/FuXi')
GMP=URIRef('http://inferenceweb.stanford.edu/registry/DPR/GMP.owl#GMP')

def GenerateProof(network,goal):
    builder=ProofBuilder(network)
    proof=builder.buildNodeSet(goal,proof=True)
    assert goal in network.inferredFacts
    return builder,proof

class ProofBuilder(object):
    """
    Handles the recursive building of a proof tree (from a 'fired' RETE-UL network), 
    keeping the state of the goals already processed

    We begin by defining a proof as a sequence of “proof steps”, where each
    proof step consists of a conclusion, a justification for that conclusion, and a set
    of assumptions discharged by the step. “A proof of C” is defined to be a proof
    whose last step has conclusion C. A proof of C is conditional on an assumption
    A if and only if there is a step in the proof that has A as its conclusion and
    “assumption” as its justification, and A is not discharged by a later step in the
    proof.    
    
    """
    def __init__(self,network):
        self.goals = {}
        self.network = network
        self.trace=[]
        self.serializedNodeSets = set()

    def serialize(self,proof,proofGraph):
        proof.serialize(self,proofGraph)
        
    def renderProof(self,proof,nsMap = {}):
        """
        Takes an instance of a compiled ProofTree and a namespace mapping (for constructing QNames
        for rule pattern terms) and returns a BGL Digraph instance representing the Proof Tree
        """
        try:    
            import boost.graph as bgl
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
        #register the step nodes
        for nodeset in self.goals.values():
            if not nodeset in visitedNodes:
                idx += 1
                visitedNodes[nodeset] = nodeset.generateBGLNode(bglGraph,vertexMaps,namespace_manager,str(idx),edgeMaps,nodeset is proof)
            #register the justification steps
            for justification in nodeset.steps:
                if not justification in visitedNodes:
                    idx += 1
                    visitedNodes[justification] = justification.generateBGLNode(bglGraph,vertexMaps,namespace_manager,str(idx),edgeMaps)
                    for ant in justification.antecedents:
                        if ant not in visitedNodes:
                            idx += 1
                            visitedNodes[ant] = ant.generateBGLNode(bglGraph,vertexMaps,namespace_manager,str(idx),edgeMaps)
                        
        nodeIdxs = {}                        
        for nodeset in self.goals.values():
            for justification in nodeset.steps:
                edge = bglGraph.add_edge(visitedNodes[nodeset],visitedNodes[justification])
                edges.append((nodeset,justification))
                
                labelMap         = edgeMaps.get('label',bglGraph.edge_property_map('string'))
                colorMap         = edgeMaps.get('color',bglGraph.edge_property_map('string'))
                labelMap[edge]   = "is the consequence of"
                colorMap[edge]   = "red"
                idMap            = edgeMaps.get('ids',bglGraph.edge_property_map('string'))
                idMap[edge]      = str(visitedNodes[nodeset]) + str(visitedNodes[justification]) + 'edge'                        
                edgeMaps['ids']   = idMap
                edgeMaps['color'] = colorMap
                edgeMaps['label'] = labelMap
                bglGraph.edge_properties['label'] = labelMap
                
                for ant in justification.antecedents:
                    edge = bglGraph.add_edge(visitedNodes[justification],visitedNodes[ant])
                    edges.append((justification,ant))
                    
                    labelMap         = edgeMaps.get('label',bglGraph.edge_property_map('string'))
                    colorMap         = edgeMaps.get('color',bglGraph.edge_property_map('string'))
                    labelMap[edge]   = "has antecedent"
                    colorMap[edge]   = "blue"
                    idMap            = edgeMaps.get('ids',bglGraph.edge_property_map('string'))
                    idMap[edge]      = str(visitedNodes[justification]) + str(visitedNodes[ant]) + 'edge'                        
                    edgeMaps['ids']   = idMap
                    edgeMaps['color'] = colorMap
                    edgeMaps['label'] = labelMap
                    bglGraph.edge_properties['label'] = labelMap
                                            
        return bglGraph
                
    def buildInferenceStep(self,parent,terminalNode,goal):
        """
        Takes a Node set and builds an inference step which contributes to its
        justification, recursively marking its ancestors (other dependent node sets / proof steps).
        So this recursive method builds a proof tree 'upwards' from the original goal
        
        This iterates over the tokens which caused the terminal node to 'fire'
        and 'prooves' them by first checking if they are inferred or if they were asserted.
        """
        #iterate over the tokens which caused the instanciation of this terminalNode
        step = InferenceStep(parent,terminalNode.clause)
        #assert len(terminalNode.instanciatingTokens) == 1,repr(terminalNode.instanciatingTokens)
        for token in terminalNode.instanciatingTokens:
            if isinstance(token,PartialInstanciation):
                _iter=token
            else:
                _iter=[token]
            for token in _iter:
                properBindings = self.network.dischargedBindings.get(goal)
#                assert properBindings
#                print properBindings, token
                if not [k for k,v in token.bindingDict.items() if properBindings[k] == v]:
                    continue
#                if not [k for k,v in token.bindingDict.items() if self.network.dischargedBindings.get(goal,{}) == v]:
#                print token
#                print token.asTuple()
                step.bindings.update(token.bindingDict)
                step.antecedents.append(self.buildNodeSet(token.asTuple(),antecedent=step))
                self.trace.append("Building inference step for %s"%parent)
                self.trace.append("Inferred from RETE node via %s"%(terminalNode.clause))                
                self.trace.append("Bindings: %s"%step.bindings)                
        assert step.antecedents
        return step
        
    def buildNodeSet(self,goal,antecedent=None,proof=False):
        if not goal in self.network.justifications:
            #Not inferred, must have been originally asserted
            #assert goal not in self.network.workingMemory
            self.trace.append("Building %s around%sgoal (justified by a direct assertion): %s"%(proof and 'proof' or 'nodeset',
                                                                                              antecedent and ' antecedent ' or '',str(buildUniTerm(goal,self.network.nsMap))))
            assertedSteps = [token.asTuple() for token in self.network.workingMemory]
            assert goal in assertedSteps
            if goal in self.goals:
                ns=self.goals[goal]
            else:
                idx=BNode()
                ns=NodeSet(goal,network=self.network,identifier=idx)
                self.goals[goal]=ns
                ns.steps.append(InferenceStep(ns,source='some RDF graph'))
        else:
            if goal in self.goals:
                ns=self.goals[goal]
            else:
                idx=BNode()
                ns=NodeSet(goal,network=self.network,identifier=idx)
                self.goals[goal]=ns
                #(register) the instanciations of justifications of the goal 
                ns.steps = [self.buildInferenceStep(ns,tNode,goal) \
                              for tNode in self.network.justifications[goal] \
                                 if self.network.instanciations[tNode]
                           ]
                self.trace.append("Building %s around%sgoal: %s"%(proof and 'proof' or 'nodeset',
                                                                antecedent and ' antecedent ' or ' ',str(buildUniTerm(goal,self.network.nsMap))))
            assert ns.steps
        return ns

class NodeSet(object):
    """
    represents a step in a proof whose conclusion is justified by any
    of a set of inference steps associated with the NodeSet. 
    
    The Conclusion of a node set represents the expression concluded by the
    proof step. Every node set has one conclusion, and a conclusion of a node
    set is of type Expression.
    
    Each inference step of a node set represents an application of an inference
    rule that justifies the node set’s conclusion. A node set can have any
    number of inference steps, including none, and each inference step of a
    node set is of type InferenceStep. A node set without inference steps is of a special kind identifying an
    unproven goal in a reasoning process as described in Section 4.1.2 below.
    
    """
    def __init__(self,conclusion=None,steps=None,identifier=BNode(),network=None):
        assert not network is None
        self.network=network
        self.identifier = identifier
        self.conclusion = conclusion
        self.language = None
        self.steps = steps and steps or []

    def serialize(self,builder,proofGraph):
#        if self.identifier in builder.serializedNodeSets:
#            return
        proofGraph.add((self.identifier,PML.hasConclusion,Literal(repr(buildUniTerm(self.conclusion,self.network.nsMap)))))
        #proofGraph.add((self.identifier,PML.hasLanguage,URIRef('http://inferenceweb.stanford.edu/registry/LG/RIF.owl')))
        proofGraph.add((self.identifier,RDF.type,PML.NodeSet))
        for step in self.steps:
            proofGraph.add((self.identifier,PML.isConsequentOf,step.identifier))
            builder.serializedNodeSets.add(self.identifier)
            step.serialize(builder,proofGraph)

    def generateBGLNode(self,bglGraph,vertexMaps,namespace_manager,idx,edgeMaps,proofRoot=False):
        vertex = bglGraph.add_vertex()
        labelMap   = vertexMaps.get('label',bglGraph.vertex_property_map('string'))        
        shapeMap   = vertexMaps.get('shape',bglGraph.vertex_property_map('string'))
        sizeMap   = vertexMaps.get('size',bglGraph.vertex_property_map('string'))
        rootMap    = vertexMaps.get('root',bglGraph.vertex_property_map('string'))
        outlineMap = vertexMaps.get('peripheries',bglGraph.vertex_property_map('string'))
        idMap      = vertexMaps.get('ids',bglGraph.vertex_property_map('string'))
        widthMap   = vertexMaps.get('width',bglGraph.vertex_property_map('string'))
        idMap[vertex] = idx
        shapeMap[vertex] = 'rectangle'
#        sizeMap[vertex] = 10
        widthMap[vertex] = '5em'
        if proofRoot:     
            rootMap[vertex] = 'true'
            outlineMap[vertex] = '1'
            labelMap[vertex] = str(repr(self))
        else:
            rootMap[vertex] = 'true'
            outlineMap[vertex] = '1'
            labelMap[vertex] = str(repr(self))
            #shapeMap[vertex] = 'plaintext'
                
        vertexMaps['ids'] = idMap
        vertexMaps['label'] = labelMap
        vertexMaps['shape'] = shapeMap
        vertexMaps['width'] = widthMap
        vertexMaps['root'] = rootMap
        vertexMaps['peripheries'] = outlineMap
#        vertexMaps['size'] = sizeMap[vertex]
        bglGraph.vertex_properties['node_id'] = idMap
        bglGraph.vertex_properties['label'] = labelMap
        bglGraph.vertex_properties['shape'] = shapeMap
    #    bglGraph.vertex_properties['width'] = widthMap
        bglGraph.vertex_properties['root'] = rootMap
        bglGraph.vertex_properties['peripheries'] = outlineMap
        return vertex
    
    def __repr__(self):
        #rt="Proof step for %s with %s justifications"%(buildUniTerm(self.conclusion),len(self.steps))
        rt="Proof step for %s"%(buildUniTerm(self.conclusion,self.network.nsMap))
        return rt
    
class InferenceStep(object):
    """
    represents a justification for the conclusion of a node set.
    
    The rule of an inference step, which is the value of the property hasRule of
    the inference step, is the rule that was applied to produce the conclusion.
    Every inference step has one rule, and that rule is of type InferenceRule
    (see Section 3.3.3). Rules are in general registered in the IWBase by engine
    developers. However, PML specifies three special instances of rules:
    Assumption, DirectAssertion, and UnregisteredRule.    

    The antecedents of an inference step is a sequence of node sets each of
    whose conclusions is a premise of the application of the inference step’s
    rule. The sequence can contain any number of node sets including none.
    The sequence is the value of the property hasAntecedent of the inference
    step.
    
    Each binding of an inference step is a mapping from a variable to a term
    specifying the substitutions performed on the premises before the application
    of the step’s rule. For instance, substitutions may be required to
    unify terms in premises in order to perform resolution. An inference step
    can have any number of bindings including none, and each binding is of
    type VariableBinding. The bindings are members of a collection that is the
    value of the property hasVariableMapping of the inference step.    

    Each discharged assumption of an inference step is an expression that is
    discharged as an assumption by application of the step’s rule. An inference
    step can have any number of discharged assumptions including none,
    and each discharged assumption is of type Expression. The discharged assumptions
    are members of a collection that is the value of the property
    hasDischargeAssumption of the inference step. This property supports
    the application of rules requiring the discharging of assumptions such as
    natural deduction’s implication introduction. An assumption that is discharged
    at an inference step can be used as an assumption in the proof
    of an antecedent of the inference step without making the proof be conditional
    on that assumption.
    
    """
    def __init__(self,parent,rule=None,bindings=None,source=None):
        self.identifier=BNode()
        self.source = source
        self.parent = parent
        self.bindings = bindings and bindings or {}
        self.rule = rule
        self.antecedents = []

    def propagateBindings(self,bindings):
        self.bindings.update(bindings)

    def serialize(self,builder,proofGraph):
        if self.rule and not self.source:
            proofGraph.add((self.identifier,PML.englishDescription,Literal(repr(self))))
        #proofGraph.add((self.identifier,PML.hasLanguage,URIRef('http://inferenceweb.stanford.edu/registry/LG/RIF.owl')))
        proofGraph.add((self.identifier,RDF.type,PML.InferenceStep))
        proofGraph.add((self.identifier,PML.hasInferenceEngine,FUXI))
        proofGraph.add((self.identifier,PML.hasRule,GMP))
        proofGraph.add((self.identifier,PML.consequent,self.parent.identifier))
        for ant in self.antecedents:
            proofGraph.add((self.identifier,PML.hasAntecedent,ant.identifier))
            ant.serialize(builder,proofGraph)
        for k,v in self.bindings.items():
            mapping=BNode()
            proofGraph.add((self.identifier,PML.hasVariableMapping,mapping))
            proofGraph.add((mapping,RDF.type,PML.Mapping))
            proofGraph.add((mapping,PML.mapFrom,k))
            proofGraph.add((mapping,PML.mapTo,v))

    def generateBGLNode(self,bglGraph,vertexMaps,namespace_manager,idx,edgeMaps):
        vertex = bglGraph.add_vertex()
        labelMap   = vertexMaps.get('label',bglGraph.vertex_property_map('string'))        
        shapeMap   = vertexMaps.get('shape',bglGraph.vertex_property_map('string'))
        #sizeMap   = vertexMaps.get('size',bglGraph.vertex_property_map('string'))
        rootMap    = vertexMaps.get('root',bglGraph.vertex_property_map('string'))
        outlineMap = vertexMaps.get('peripheries',bglGraph.vertex_property_map('string'))
        idMap      = vertexMaps.get('ids',bglGraph.vertex_property_map('string'))
        #widthMap   = vertexMaps.get('width',bglGraph.vertex_property_map('string'))
        idMap[vertex] = idx
        #shapeMap[vertex] = 'box'
        shapeMap[vertex] = 'plaintext'
        #sizeMap[vertex] = '10'
        #outlineMap[vertex] = '1'
        if self.source:
            labelMap[vertex]=str(self)
        else:
            labelMap[vertex]=str(self)
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

    def __repr__(self):
        rt=self.source and "[Parsing RDF source]" or repr(self.rule)#"%s\n%s"%(repr(self.rule),'\n'.join(['%s=%s'%(k,v) for k,v in self.bindings.items()]))
        return rt

class Expression(object):
    def __init__(self):
        pass

#__test__ = { 'NodeSet': _modinv02, '_modpre01b': _modpre01b,
#             '_modpst01b': _modpst01b }

#def _test():
#    import contract, doctest, Proof
#    contract.checkmod(Proof, contract.CHECK_ALL)
#    return doctest.testmod(Proof)
#
#if __name__ == '__main__':
#    t = _test()
#    if t[0] == 0:
#        print "test: %d tests succeeded" % t[1]
#    else:
#        print "test: %d/%d tests failed" % t


