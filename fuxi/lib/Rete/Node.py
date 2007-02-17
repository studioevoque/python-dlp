"""
This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 2.5 License.
To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-sa/2.5/ 
or send a letter to Creative Commons, 543 Howard Street, 5th Floor, San Francisco, California, 94105, USA.
"""

class Node:
    """
    A node in a Rete network.  Behavior between Alpha and Beta (Join) nodes
    """
    def connectToBetaNode(self,betaNode,position):
        from BetaNode import BetaNode, LEFT_MEMORY, RIGHT_MEMORY, PartialInstanciation
        self.descendentMemory.append(betaNode.memories[position])
        self.descendentBetaNodes.add(betaNode)        