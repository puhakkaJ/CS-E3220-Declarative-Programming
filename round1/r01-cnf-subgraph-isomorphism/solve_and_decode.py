"""Solve an encoding produced with encode.ancode with a SAT solver,
decode its solution, and check the the solution is a valid k-coloring."""

#
# Author: Tommi Junttila, Aalto University.
# Only personal student use on the Aalto University course
# CS-E3220 Declarative Programming is allowed.
# Redistribution in any form, including posting to public or
# shared repositories or forums, is not allowed.
#

# Do NOT edit or add the import statements
from typing import Tuple

from pysat.formula import CNF
from pysat.solvers import Solver
from graph import Graph


class ModelValidationError(Exception):
    """An exception raised if the solution validation fails."""
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return self.value


def solve_and_decode(pattern: Graph, target: Graph, cnf: CNF,
                     max_solutions: int,
                     print_solutions: bool) -> None:
    """Solve and decode the solutions of the given
    propositional CNF SAT instance
    encoding an induced sub-graph isomorphism problem instance.
    Do NOT modify this method."""

    def err(msg: str):
        raise ModelValidationError(msg)

    # The number of the encoding variables in the instance.
    nof_encoding_vars = pattern.nof_vertices * target.nof_vertices

    def m_var(cnf_var: int) -> Tuple[int, int]:
        """The inverse of the encode.m_cnf method.
        Given a CNF variable for the encoding variable m_{p_vertex, t_vertex},
        return the parameters p_vertex and t_vertex."""
        assert 1 <= cnf_var <= nof_encoding_vars
        t_vertex = ((cnf_var - 1) // pattern.nof_vertices) + 1
        p_vertex = ((cnf_var - 1) % pattern.nof_vertices) + 1
        assert 1 <= p_vertex <= pattern.nof_vertices
        assert 1 <= t_vertex <= target.nof_vertices
        assert (t_vertex-1)*pattern.nof_vertices+(p_vertex-1)+1 == cnf_var
        return (p_vertex, t_vertex)

    # Create a solver and give the CNF encoding to it
    solver = Solver(bootstrap_with=cnf)

    # Enumerate and verify all solutions
    nof_solutions = 0
    for model in solver.enum_models():
        isomorphism = {}
        for literal in model:
            if 0 < literal <= nof_encoding_vars:
                (p_vertex, t_vertex) = m_var(literal)
                if p_vertex in isomorphism:
                    err(f'Found a solution with two images '
                        f'for the pattern vertex {p_vertex}')
                isomorphism[p_vertex] = t_vertex
        isomorphism_inv = {}
        for p_vertex in range(1, pattern.nof_vertices):
            if p_vertex not in isomorphism:
                err(f'A solution with no image for '
                    f'the pattern vertex {p_vertex}')
            t_vertex = isomorphism[p_vertex]
            if t_vertex in isomorphism_inv:
                err(f'A solution with non-injective mapping: '
                    f'the target vertex {t_vertex} is the image of '
                    f'multiple pattern vertices')
            isomorphism_inv[t_vertex] = p_vertex
        # Check that adjacency is preserved
        for (p1, p2) in pattern.edges:
            if not target.has_edge(isomorphism[p1], isomorphism[p2]):
                err(f'A solution that does not preserve adjancency: '
                    f'the pattern has an edge between {p1} and {p2} but '
                    f'the target does not have an edge between '
                    f'{isomorphism[p1]} and {isomorphism[p2]}')
        # Check that non-adjacency is preserved
        for p1 in range(1, pattern.nof_vertices+1):
            for p2 in range(p1+1, pattern.nof_vertices+1):
                if (p1, p2) in pattern.edges:
                    continue
                if target.has_edge(isomorphism[p1], isomorphism[p2]):
                    err(f'A solution that does not preserve non-adjancency: '
                        f'the pattern does not have an edge between '
                        f'{p1} and {p2} '
                        f'but the target has an edge between '
                        f'{isomorphism[p1]} and {isomorphism[p2]}')
        nof_solutions += 1
        if print_solutions:
            print('Solution: '+str(isomorphism))
        if 0 < max_solutions <= nof_solutions:
            break
    print(f'Found {nof_solutions} solutions')
