import argparse
import random
import sys
import csv
import os.path
import tempfile
import subprocess
import logging
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import List, Tuple


@dataclass
class Graph:
    nodes: List[str]
    edges: List[Tuple[str, str]]

    @classmethod
    def empty(cls):
        return cls(nodes=[], edges=[])

    def add_node(self):
        index = len(self.nodes)
        node = f"n{index}"
        self.nodes.append(node)
        return node


@dataclass
class ConnectivityProblem:
    graph: Graph
    src: str
    dst: str


def single_path_connectivity_problem(n):
    """
    Generates a connectivity problem that's just traversing a single path graph
    of length n from beginning to end.
    """
    g = Graph.empty()
    src = g.add_node()
    dst = src
    for i in range(n):
        last = dst
        dst = g.add_node()
        g.edges.append((last, dst))
    return ConnectivityProblem(
        graph=g,
        src=src,
        dst=dst
    )


def random_graph_growth(g, n):
    for i in range(n):
        # Pick a random current node as a source.
        connected_node = random.choice(g.nodes)

        # Generate a new node.
        new_node = g.add_node()

        # Update graph structure.
        g.edges.append((connected_node, new_node))


def random_connectivity_problem(n):
    assert n > 0
    m = n//2
    p = single_path_connectivity_problem(m)
    random_graph_growth(p.graph, n-m)
    random.shuffle(p.graph.edges)
    return p


def write_graph_facts(g, out=sys.stdout):
    # Nodes.
    for node in g.nodes:
        print(f'node("{node}").', file=out)

    # Edges (directional).
    for a, b in g.edges:
        print(f'edge("{a}", "{b}").', file=out)


def write_connectivity_problem_facts(p, out=sys.stdout):
    write_graph_facts(p.graph, out=out)
    print(f'source("{p.src}").', file=out)
    print(f'destination("{p.dst}").', file=out)


def write_datalog(p, out):
    # Facts.
    write_connectivity_problem_facts(p, out=out)

    # Rules.
    print('connected(A, B) :- edge(A, B).', file=out)
    print('connected(A, B) :- edge(A, M), connected(M, B).', file=out)

    print('go :- source(S), destination(D), connected(S,D).')

def main():
    write_datalog(random_connectivity_problem(100), sys.stdout)

if __name__ == "__main__":
    main()
