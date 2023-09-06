#
# Author: Tommi Junttila, Aalto University.
# Only personal student use on the Aalto University course
# CS-E3220 Declarative Programming is allowed.
# Redistribution in any form, including posting to public or
# shared repositories or forums, is not allowed.
#

# Do NOT edit or add the import statements
import re
from typing import Set, Tuple

def read_graph(filename: str) -> Tuple[int, Set[Tuple[int, int]]]:
    """Read the graph from the given file.
    Returns a pair (n, edges), such that
    - "n" is the number of the vertices in the graph,
    - the vertices are represented with integers from 1 to n, and
    - "edges" is the set of edges in the graph, each edge being
      a pair (v1, v2) with v1 < v2.
    Do NOT modify this method.
    """
    with open(filename, 'r', encoding='UTF-8') as f:
        # First line: the number of vertices
        nof_vertices = int(f.readline())
        assert 1 <= nof_vertices
        # Second line: the edges
        pattern = re.compile(r'\((\d+),(\d+)\)')
        iterator = pattern.finditer(f.readline().strip())
        edges = set()
        for match in iterator:
            (v1, v2) = (int(match.group(1)), int(match.group(2)))
            assert 1 <= v1 <= nof_vertices
            assert 1 <= v2 <= nof_vertices
            if v1 == v2:
                # Skip self-loops
                continue
            if v1 < v2:
                edges.add((v1, v2))
            else:
                edges.add((v2, v1))
        return (nof_vertices, edges)
