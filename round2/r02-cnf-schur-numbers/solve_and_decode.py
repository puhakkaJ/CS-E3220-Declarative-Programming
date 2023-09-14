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


class ModelValidationError(Exception):
    """An exception raised if the solution validation fails."""
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return self.value

def solution_as_str(solution) -> str:
    """Transform a coloring into a string.
    Used for hashing as solutions (dictionaries) are not hashable in Python."""
    return '{'+(', '.join([f'{i}->{solution[i]}' for
                           i in sorted(solution.keys())]))+'}'

def solve_and_decode(n: int, nof_colors: int, break_symmetries: bool,
                     cnf: CNF,
                     max_solutions: int, print_solutions: bool) -> None:
    """Solve and decode the solutions of the given
    popositional CNF SAT instance
    encoding an integer interval coloring problem instance.
    Do NOT modify this method."""

    def err(msg: str):
        raise ModelValidationError(msg)

    # The number of the encoding variables in the instance.
    nof_encoding_vars = n * nof_colors

    def v_var(cnf_var: int) -> Tuple[int, int]:
        """The inverse of the encode.v_cnf method.
        Given a CNF variable for the encoding variable v_{i, c},
        return the parameters i and c."""
        assert 1 <= cnf_var <= nof_encoding_vars
        i = ((cnf_var - 1) // nof_colors) + 1
        c = ((cnf_var - 1) % nof_colors) + 1
        assert 1 <= i <= n
        assert 1 <= c <= nof_colors
        assert (i-1)*nof_colors+(c-1)+1 == cnf_var
        return (i, c)

    def canonize_solution(solution):
        seen = set()
        seen_order = []
        for i in sorted(solution.keys()):
            if not solution[i] in seen:
                seen_order.append(solution[i])
                seen.add(solution[i])
        perm = {}
        for (index, i) in enumerate(seen_order):
            perm[i] = index+1
        canonical_solution = {}
        for i in sorted(solution.keys()):
            canonical_solution[i] = perm[solution[i]]
        return canonical_solution

    # Create a solver and give the CNF encoding to it
    solver = Solver(bootstrap_with=cnf)

    # Enumerate and verify all solutions
    solutions = []
    for model in solver.enum_models():
        solution = {}
        for literal in model:
            if 0 < literal <= nof_encoding_vars:
                (i, color) = v_var(literal)
                if i in solution:
                    err(f'Found a solution with two colors for the value {i}')
                solution[i] = color
        for i in range(1, n+1):
            if i not in solution:
                err(f'A solution with no color for the value {i}')
        for x in range(1, n+1):
            for y in range(x, n-x+1):
                z = x+y
                if solution[x] == solution[y] and solution[x] == solution[z]:
                    err(f'A solution where the values {x}, {y}, and {z} '
                        f'have the same color {solution[x]} but {x}+{y}={z}')
        solutions.append(solution)
        if print_solutions:
            print('Solution: '+str(solution))
        if 0 < max_solutions <= len(solutions):
            break

    if len(solutions) != 0:
        seen = set()
        for solution in solutions:
            solution_str = solution_as_str(solution)
            if solution_str in seen:
                err(f'The same solution is seen twice: {solution}')
            else:
                seen.add(solution_str)

    if break_symmetries and len(solutions) != 0:
        seen = {}
        for solution in solutions:
            canonical_solution = canonize_solution(solution)
            canonical_solution_str = solution_as_str(canonical_solution)
            if canonical_solution_str in seen:
                err(f'Two isomorphic solutions found: '
                    f'{solution} and {seen[canonical_solution_str]}')
            else:
                seen[canonical_solution_str] = solution

    print(f'Found {len(solutions)} solutions')
