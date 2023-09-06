#
# Author: Tommi Junttila, Aalto University.
# Only personal student use on the Aalto University course
# CS-E3220 Declarative Programming is allowed.
# Redistribution in any form, including posting to public or
# shared repositories or forums, is not allowed.
#

"""Encode an induced sub-graph isomorphism problem to a CNF SAT instance."""

# Do not change or add import statements
from pysat.formula import CNF
from graph import Graph


def encode(pattern: Graph, target: Graph) -> CNF:
    """Encode the induced sub-graph isomorhism problem between
    pattern and target graphs to CNF SAT problem."""

    # A helper function that you *should* use!
    # Do NOT modify
    def m_cnf(p_vertex: int, t_vertex: int):
        """Return the positive integer CNF variable number
        of the encoding variable m_{p_vertex,t_vertex} denoting that
        the pattern vertex p_vertex is mapped to the target vertex t_vertex."""
        assert 1 <= p_vertex <= pattern.nof_vertices
        assert 1 <= t_vertex <= target.nof_vertices
        return (t_vertex-1)*pattern.nof_vertices+(p_vertex-1)+1

    # The number of variables in the instance,
    # at least pattern.nof_vertices * target.nof_vertices
    # Do NOT modify
    nof_vars = pattern.nof_vertices * target.nof_vertices

    # A helper function that you may use (you do not have to).
    # If you use auxiliary variables, make sure that they do not introduce
    # extra models, i.e. models that are the same when projected to
    # the important variables of form m_{p,v}.
    # Do NOT modify
    def new_aux_variable():
        """Allocate a new auxiliary CNF variable."""
        nonlocal nof_vars
        nof_vars += 1
        return nof_vars

    # The clauses in the CNF instance.
    # To add a clause such as (m_{1,1} | !m_{1,2} | !m_{1,3}),
    # write cnf.append([m_cnf(1,1), -m_cnf(1,2), -m_cnf(1,3)])
    cnf = CNF()

    # INSERT YOUR CODE HERE
    # It should only add appropriate clauses to "clauses" as descibed above.
    # The CNF ecoding should be such that each satisfying truth assignment,
    # when projected to the m_{p,v} literals,
    # corresponds to an induced subgraph isomorphism m as follows:
    # if m_{p,v} is true, then m(p) = v.
    # Thus you should encode the following constraints in CNF:
    # - The m_{p,v} literals encode an injection m
    #   from the pattern graph vertices {1,...,pattern.nof_vertices}
    #   to the target graph vertices {1,...,target.nof_vertices}.
    # - The injection m encoded by the m_{p,v} literals preserves both
    #   adjacency (existence of edges between vertices)
    #   as well as
    #   non-adjacency (non-existence of edges between vertices).
    # See the file graph.py for the graph interface allowing one to
    # obtain the edge relations of the pattern and target graphs in question.

    # Every vertex in pattern should be mapped to some vertex in target
    for p in range(1, pattern.nof_vertices + 1):
        cnf.append([m_cnf(p, t) for t in range(1, target.nof_vertices + 1)])

    # Two different vertices should not be mappet to same vertex
    for t in range(1, target.nof_vertices + 1):
        for p1 in range(1, pattern.nof_vertices + 1):
            for p2 in range(p1 + 1, pattern.nof_vertices + 1):
                cnf.append([-m_cnf(p1, t), -m_cnf(p2, t)])

    # Verticex should not be mappet to two different vertices
    for p in range(1, pattern.nof_vertices + 1):
        for t1 in range(1, target.nof_vertices + 1):
            for t2 in range(t1 + 1, target.nof_vertices + 1):
                cnf.append([-m_cnf(p, t1), -m_cnf(p, t2)])
    
    # An edge in pattern cannot be mapped to a non-edge in target and vice-versa
    for p1 in range(1, pattern.nof_vertices + 1):
        for p2 in range(p1 + 1, pattern.nof_vertices + 1):
            for t1 in range(1, target.nof_vertices + 1):
                for t2 in range(1, target.nof_vertices + 1):
                    # An edge can not be mapped to a non-edge or a non-edge can not be mapped to an edge
                    if (pattern.has_edge(p1, p2) and not target.has_edge(t1, t2)) or (not pattern.has_edge(p1, p2) and target.has_edge(t1, t2)):
                        cnf.append([-m_cnf(p1, t1), -m_cnf(p2, t2)])
    
    return cnf
