
# OBDD

import math

# This is for the 'reduce' function.

from functools import reduce

# Truth-tables for commonly used binary connectives

def AND(b1,b2):
    if b1==1 and b2==1:
        return 1
    else:
        return 0
    
def OR(b1,b2):
    if b1==1 or b2==1:
        return 1
    else:
        return 0

def XOR(b1,b2):
    if b1==b2:
        return 0
    else:
        return 1

def EQVI(b1,b2):
    if b1==b2:
        return 1
    else:
        return 0

def IMPL(b1,b2):
    if b1 <= b2:
        return 1
    else:
        return 0

# Type of non-terminal OBDD nodes
#    nodeVar : the variable in the node
#    posChild : the sub-OBDD when nodeVar is true
#    negChild : the sub-OBDD when nodeVar is false
#
# The two terminal nodes are represented by the integers 0 and 1,
# with the usual meaning of 0 being FALSE and 1 being TRUE.

class OBDDnode():
    def __init__(self,nodeVar,posChild,negChild):
        self.nodeVar = nodeVar
        self.posChild = posChild
        self.negChild = negChild
        self.modelCount = 0

# Class for an OBDD with a given variable ordering, and with
# each subgraph induced by a node representing a Boolean function.

class OBDD():

    # Initialize an OBDD with a given variable ordering.

    def __init__(self,vars):

        # 'vars' is a list of variable names (strings), indicating
        # the variable ordering of the OBDD.

        self.vars = vars

        # 'hash' is a dictionary for mapping var, child1, child2 to
        # the unique OBDD node with these properties.

        self.hash = dict()

        # 'varIndex' is a mapping from variables to their indices.

        self.varIndex = dict()
        for i in range(0,len(vars)):
            self.varIndex[vars[i]] = i

    # Create a new node if one does not already exist.
    # Must check that child1 and child2 are different:
    # if they are the same, return the child directly,
    # without creating a new node. This is the property
    # of being 'reduced'.

    def newOBDDnode(self,rootVar,child1,child2):
        if child1 == child2:
            return child1
        if (rootVar,child1,child2) in self.hash:
            return self.hash[(rootVar,child1,child2)]
        newNode = OBDDnode(rootVar,child1,child2)
        self.hash[(rootVar,child1,child2)] = newNode

        # Do model-count

        def modelcount(node):
            if node == 1:
                return 1
            elif node == 0:
                return 0

            if type(node.posChild) == int:
                i1 = len(self.vars)
            else:
                i1 = self.varIndex[node.posChild.nodeVar]

            if type(node.negChild) == int:
                i0 = len(self.vars)
            else:
                i0 = self.varIndex[node.negChild.nodeVar]

            i = self.varIndex[node.nodeVar]
       
            count = pow(2, (i1-i-1)) * modelcount(node.posChild) + pow(2,(i0-i-1)) * modelcount(node.negChild)

            return count

            
        # Store model-count

        newNode.modelCount = modelcount(newNode)

        return newNode

    # The APPLY operation for two OBDD nodes.
    # 'f' is the Boolean function to be applied at
    # leaf nodes.

    def apply(self,f,b1,b2):
        if isinstance(b1,int) and isinstance(b2,int):
            return f(b1,b2)
        if isinstance(b1,int) and isinstance(b2,OBDDnode):
            return self.newOBDDnode(b2.nodeVar,
                                    self.apply(f,b1,b2.posChild),
                                    self.apply(f,b1,b2.negChild))
        elif isinstance(b1,OBDDnode) and isinstance(b2,int):
            return self.newOBDDnode(b1.nodeVar,
                                    self.apply(f,b1.posChild,b2),
                                    self.apply(f,b1.negChild,b2))
        else:
            root1 = b1.nodeVar
            root2 = b2.nodeVar

            if root1==root2:
                return self.newOBDDnode(root1,
                                     self.apply(f,b1.posChild,b2.posChild),
                                     self.apply(f,b1.negChild,b2.negChild))

            if self.varIndex[root1] < self.varIndex[root2]:
                rootVar = root1
                child1 = self.apply(f,b1.posChild,b2)
                child2 = self.apply(f,b1.negChild,b2)
            else:
                rootVar = root2
                child1 = self.apply(f,b1,b2.posChild)
                child2 = self.apply(f,b1,b2.negChild)

            return self.newOBDDnode(rootVar,child1,child2)

    # Return the model-count of a BDD node, taking into account variables
    # before the root node in the variable ordering.

    def countModels(self,b):
        return b.modelCount * round(math.pow(2, self.varIndex[b.nodeVar]))

    # Constructors for OBDDs
    #
    # Create an OBDD representing an atomic propositions.

    def atom(self,a):
        return self.newOBDDnode(a,1,0)

    # Constructors for common Boolean functions:
        
    def conj(self,b1,b2):
        return self.apply(AND,b1,b2)

    def disj(self,b1,b2):
        return self.apply(OR,b1,b2)

    def neg(self,b):
        return self.apply(XOR,b,1)

    def impl(self,b1,b2):
        return self.apply(IMPL,b1,b2)

    def eqvi(self,b1,b2):
        return self.apply(EQVI,b1,b2)

    # Chain conjunction and disjunction

    def conjs(self,bb):
        return reduce(self.conj,bb,1)

    def disjs(self,bb):
        return reduce(self.disj,bb,0)

    # Visualize an OBDD as a graph

    def show(self,bdd,filename):
        import pygraphviz as pgv
        G = pgv.AGraph(directed=True)

        visited = set()

        def visitAll(bddnode):

            # Already visualized?
            if bddnode in visited:
                return

            # Mark as already visualized.
            visited.update({bddnode})

            if isinstance(bddnode,int):
                # Visualize terminal nodes.
                if bddnode == 0:
                    G.add_node("F")
                else:
                    G.add_node("T")
                # End recursive call.
                return

            # Visualize node, with unique object ID as name, and
            # variable name as the node label.
            G.add_node(str(id(bddnode)))
            n = G.get_node(str(id(bddnode)))
            n.attr["label"] = bddnode.nodeVar
            if bddnode.modelCount > 0:
                n.attr["xlabel"] = str(bddnode.modelCount)

            # Visualize child nodes recursively.
            visitAll(bddnode.posChild)
            visitAll(bddnode.negChild)

            # Draw arc to the positive child node.

            if bddnode.posChild == 0:
                G.add_edge(str(id(bddnode)),"F", color="green")
            elif bddnode.posChild == 1:
                G.add_edge(str(id(bddnode)),"T", color="green")
            else:
                G.add_edge(str(id(bddnode)),str(id(bddnode.posChild)), color="green")

            # Draw arcs to the negative child node.
            
            if bddnode.negChild == 0:
                G.add_edge(str(id(bddnode)),"F", color="red",style = "dashed")
            elif bddnode.negChild == 1:
                G.add_edge(str(id(bddnode)),"T", color="red",style = "dashed")
            else:
                G.add_edge(str(id(bddnode)),str(id(bddnode.negChild)), color="red",style = "dashed")

        # Visualize all nodes by calling the root.
        
        visitAll(bdd)

        # Use Dot for layout (better for directed graphs!)

        G.layout(prog='dot')

        # Output

        G.draw(filename)

# Run some tests.

if __name__ == "__main__":
    BDD = OBDD(["A","B","C","D"])

    A = BDD.atom("A")
    B = BDD.atom("B")
    C = BDD.atom("C")
    D = BDD.atom("D")

    BDD.show(BDD.conjs([]),"TRUE.png")
    BDD.show(BDD.disjs([]),"FALSE.png")
    BDD.show(B,"B.png")
    BDD.show(A,"A.png")
    BDD.show(BDD.neg(A),"negA.png")
    BDD.show(BDD.conjs([A,B]),"conjAB.png")
    BDD.show(BDD.conjs([A,B,C]),"conjABC.png")
    BDD.show(BDD.conjs([A,B,C,D]),"conjABCD.png")
    BDD.show(BDD.conj(BDD.eqvi(A,B),BDD.eqvi(C,D)),"eqviABCD.png")
    BDD.show(BDD.conj(BDD.eqvi(A,D),BDD.eqvi(B,C)),"eqviADBC.png")
    BDD.show(BDD.conj(BDD.eqvi(A,C),BDD.eqvi(B,D)),"eqviACBD.png")

    BDD2 = OBDD([ "X" + str(i) for i in range(0,4) ] + [ "Y" + str(i) for i in reversed(range(0,4)) ])
    BDD2.show(BDD2.conjs([BDD2.eqvi(BDD2.atom("X" + str(i)),BDD2.atom("Y" + str(i))) for i in range(0,4)]),"chainXYeqvi.png")
    
    BDD3 = OBDD([ f(i) for i in range(0,4) for f in (lambda x : "X" + str(x), lambda y : "Y" + str(y)) ])
    BDD3.show(BDD3.conjs([BDD3.eqvi(BDD3.atom("X" + str(i)),BDD3.atom("Y" + str(i))) for i in range(0,4)]),"chainXYeqviInterleaved.png")
