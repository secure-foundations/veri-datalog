import argparse
import random
import sys
import os.path
import tempfile
import subprocess
import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import List, Tuple


@dataclass
class Graph:
    nodes: List[str]
    edges: List[Tuple[str, str]]


def random_connected_graph(n):
    assert n > 0, ""

    def node_name(i):
        return f"n{i}"

    # Start with a single-node graph.
    g = Graph(nodes=[node_name(0)], edges=[])

    # Iteratively add nodes, each connected to one already in the graph.
    while len(g.nodes) < n:
        # Generate a new node.
        new_node = node_name(len(g.nodes))

        # Pick a random current node to connect it to.
        connected_node = random.choice(g.nodes)

        # Update graph structure.
        g.nodes.append(new_node)
        g.edges.append((connected_node, new_node))

    return g


def write_graph_facts(g, out=sys.stdout):
    # Nodes.
    for node in g.nodes:
        print(f'node("{node}").', file=out)

    # Edges.
    for edge in g.edges:
        print(f'edge("{edge[0]}", "{edge[1]}").', file=out)


class Solver(ABC):
    @abstractmethod
    def name(self):
        raise NotImplementedError()

    @abstractmethod
    def solve(self, g):
        raise NotImplementedError()


class DafnySolver(Solver):
    def __init__(self, name, path):
        self._name = name
        self._path = path

    def name(self):
        return self._name

    def solve(self, g):
        with tempfile.NamedTemporaryFile(mode='w') as temp:
            # Write the problem.
            with temp.file as f:
                self._write_datalog(g, out=f)

            # Invoke the solver.
            project = os.path.join(self._path, "datalog/datalog.csproj")
            args = ["dotnet", "run", "--project", project, temp.name]
            result = subprocess.run(args, check=True, capture_output=True)

    @staticmethod
    def _write_datalog(g, out):
        # Facts.
        write_graph_facts(g, out=out)

        # Rules.
        print('connected(A, B) :- edge(A, B).', file=out)
        print('connected(A, B) :- connected(A, M), edge(M, B).', file=out)

        # Query.
        print(f'query(W) :- connected("{g.nodes[0]}", W).', file=out)


class SouffleSolver(Solver):
    def __init__(self, name="souffle"):
        self._name = name

    def name(self):
        return self._name

    def solve(self, g):
        with tempfile.NamedTemporaryFile(mode='w') as temp:
            # Write the problem.
            with temp.file as f:
                self._write_program(g, out=f)

            # Invoke the solver.
            args = ["souffle", temp.name]
            result = subprocess.run(args, check=True, capture_output=True)

    @staticmethod
    def _write_program(g, out):
        print('.decl node( a:symbol )', file=out)
        print('.decl edge( a:symbol, b:symbol )', file=out)

        # Facts.
        write_graph_facts(g, out=out)

        # Rules.
        print('.decl connected( a:symbol, b:symbol )', file=out)
        print('connected(A, A) :- node(A).', file=out)
        print('connected(A, B) :- connected(A, M), edge(M, B).', file=out)

        # Query.
        print('.decl query( a:symbol )', file=out)
        print('.printsize query', file=out)
        print(f'query(W) :- connected("{g.nodes[0]}", W).', file=out)


def main(args):
    logging.basicConfig(level=logging.INFO)

    # Options.
    parser = argparse.ArgumentParser(
                        prog='benchmark',
                        description='Benchmark datalog solvers.')
    parser.add_argument('--nodes', default=10, type=int, help="Number of nodes in the graph.")
    parser.add_argument('--root', default="../..", help="Path to veri-datalog repository root.")

    opts = parser.parse_args(args)

    # Solvers.
    solvers = [
        DafnySolver("bottom-up", os.path.join(opts.root, "dafny", "bottom-up")),
        DafnySolver("top-down", os.path.join(opts.root, "dafny", "top-down")),
        SouffleSolver(),
    ]
    for solver in solvers:
        logging.debug("configured solver: %s", solver.name())

    # Generate.
    g = random_connected_graph(opts.nodes)
    logging.info("generated graph problem with %d nodes", len(g.nodes))

    # Solve.
    for solver in solvers:
        logging.info("execute solver: %s", solver.name())
        solver.solve(g)


if __name__ == "__main__":
    main(sys.argv[1:])
