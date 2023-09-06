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
from typing import Set, Tuple

from pysat.formula import CNF
from pysat.solvers import Solver


class ModelValidationError(Exception):
    """An exception raised if the solution validation fails."""
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return self.value


def solve_and_decode(nof_vertices: int, edges: Set[Tuple[int, int]],
                     nof_colors: int, cnf: CNF,
                     all_solutions: bool,
                     print_solutions: bool) -> None:
    """Solve and decode the solutions of the given
    propositional CNF SAT instance
    encoding a k-coloring instance.
    Do NOT modify this method."""

    def err(msg: str):
        raise ModelValidationError(msg)

    # The number of the encoding variables in the instance.
    nof_encoding_vars = nof_vertices * nof_colors

    def xvar_inv(cnf_var: int) -> Tuple[int, int]:
        """The inverse of the encode.xvar method.
        Given the CNF variable number corresponding to
        the encoding variable x_{vertex,color}
        denoting that "vertex" should be colored with "color",
        return the parameters "vertex" and "color"."""
        assert 1 <= cnf_var <= nof_encoding_vars
        vertex = ((cnf_var - 1) // nof_colors) + 1
        color = ((cnf_var - 1) % nof_colors) + 1
        assert 1 <= vertex <= nof_vertices
        assert 1 <= color <= nof_colors
        assert (vertex-1)*nof_colors+(color-1)+1 == cnf_var
        return (vertex, color)

    # Create a solver and give the CNF encoding to it
    solver = Solver(bootstrap_with=cnf)

    # Enumerate and verify all solutions
    nof_solutions = 0
    for model in solver.enum_models():
        vertex_colors = {}
        for literal in model:
            if literal > 0 and abs(literal) <= nof_encoding_vars:
                (vertex, color) = xvar_inv(literal)
                if vertex in vertex_colors:
                    err(f'Found a solution with two colors '
                        f'for the vertex {vertex}')
                vertex_colors[vertex] = color
        for vertex in range(1, nof_vertices+1):
            if vertex not in vertex_colors:
                err(f'Found a solution with no color for the vertex {vertex}')
        for (vertex1, vertex2) in edges:
            if vertex_colors[vertex1] == vertex_colors[vertex2]:
                err(f'Found a solution where '
                    f'the vertices {vertex1} and {vertex2} '
                    f'have the same color but there is an edge between them')
        nof_solutions += 1
        if print_solutions:
            print('Solution: '+str(vertex_colors))
        if not all_solutions:
            break
    print(f'Found {nof_solutions} solutions')
