"""A simple class for undirected loop-free graphs."""

#
# Author: Tommi Junttila, Aalto University.
# Only personal student use on the Aalto University course
# CS-E3220 Declarative Programming is allowed.
# Redistribution in any form, including posting to public or
# shared repositories or forums, is not allowed.
#

import re


class Graph:
    """
    A simple class for undirected loop-free graphs.
    Do NOT modify.
    """
    def __init__(self):
        """The number of vertices in the graph.
        The vertices are represented with the integers {1,2,...,n}."""
        self.nof_vertices = 0
        """The edges of the graph,
        each edge being a pair (v1,v2) where v1 < v2."""
        self.edges = set()
        """
        Neighbourhood relation derived from the edges.
        v1 is in neighbours[v2] if and only if {v1,v2} is an edge in the graph.
        """
        self.neighbours = {}

    def has_edge(self, vertex1: int, vertex2: int) -> bool:
        """Does this graph have an edge between vertex1 and vertex2?"""
        assert 1 <= vertex1 <= self.nof_vertices
        assert 1 <= vertex2 <= self.nof_vertices
        return vertex2 in self.neighbours[vertex1]

    @staticmethod
    def read(filename: str):
        """
        Read the graph from the given file.
        After this:
        - The variable "nof_variables" contains the number of vertices.
          The vertices are represented with integers {1,2,...,n}.
        - The variable "edges" is the set of edges in the graph,
          each edge being a pair (v1,v2) where v1 < v2.
        Do NOT modify
        """
        graph = Graph()
        with open(filename, 'r', encoding='UTF-8') as handle:
            # First line: the number of vertices
            graph.nof_vertices = int(handle.readline())
            # Initialize neighbour sets to empty
            for vertex in range(1, graph.nof_vertices+1):
                graph.neighbours[vertex] = set()
            # Second line: the edges
            pattern = re.compile(r'\((\d+),(\d+)\)')
            iterator = pattern.finditer(handle.readline().strip())
            for match in iterator:
                (vertex1, vertex2) = (int(match.group(1)), int(match.group(2)))
                assert 1 <= vertex1 <= graph.nof_vertices
                assert 1 <= vertex2 <= graph.nof_vertices
                if vertex1 == vertex2:
                    continue  # Skip self-loops
                if vertex1 < vertex2:
                    graph.edges.add((vertex1, vertex2))
                else:
                    graph.edges.add((vertex2, vertex1))
                graph.neighbours[vertex1].add(vertex2)
                graph.neighbours[vertex2].add(vertex1)
        return graph
