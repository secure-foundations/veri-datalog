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


@dataclass
class ConnectivityProblem:
    graph: Graph
    src: str
    dst: str


def random_connectivity_problem(n):
    g = random_connected_graph(n)
    assert n >= 2
    src, dst = random.sample(g.nodes, 2)
    return ConnectivityProblem(
        graph=g,
        src=src,
        dst=dst
    )


def write_graph_facts(g, out=sys.stdout):
    # Nodes.
    for node in g.nodes:
        print(f'node("{node}").', file=out)

    # Edges (bi-directional).
    for a, b in g.edges:
        print(f'edge("{a}", "{b}").', file=out)
        print(f'edge("{b}", "{a}").', file=out)


def write_connectivity_problem_facts(p, out=sys.stdout):
    write_graph_facts(p.graph, out=out)
    print(f'source("{p.src}").', file=out)
    print(f'destination("{p.dst}").', file=out)


@dataclass
class Result:
    process: subprocess.CompletedProcess
    elapsed_ns: int


def benchmark_subprocess(args, **kwargs):
    logging.debug(args)

    start = time.perf_counter_ns()
    process = subprocess.run(args, check=True, capture_output=True, **kwargs)
    end = time.perf_counter_ns()

    logging.debug(process.stdout)
    return Result(
        process=process,
        elapsed_ns=end-start,
    )


class Solver(ABC):
    QUERY_NAME = 'query'

    @abstractmethod
    def name(self):
        raise NotImplementedError()

    @abstractmethod
    def solve(self, p, timeout=None, debug=False):
        raise NotImplementedError()


class DafnySolver(Solver):
    def __init__(self, name, path, match_output):
        self._name = name
        self._path = path
        self._match_output = match_output

    def name(self):
        return self._name

    def solve(self, p, timeout=None, debug=False):
        with tempfile.NamedTemporaryFile(mode='w', delete=not debug) as temp:
            # Write the problem.
            with temp.file as f:
                self._write_datalog(p, out=f)

            # Invoke the solver.
            project = os.path.join(self._path, "datalog/datalog.csproj")
            args = ["dotnet", "run", "--project", project, temp.name]
            result =  benchmark_subprocess(args, timeout=timeout)

            assert result.process.returncode == 0
            assert self._match_output in result.process.stdout

            return result

    @classmethod
    def _write_datalog(cls, p, out):
        # Facts.
        write_connectivity_problem_facts(p, out=out)

        # Rules.
        print('connected(A, B) :- edge(A, B).', file=out)
        print('connected(A, B) :- edge(A, M), connected(M, B).', file=out)

        # Query.
        print(f'{cls.QUERY_NAME}(S, D) :- source(S), destination(D), connected(S, D).', file=out)


class SouffleSolver(Solver):
    def __init__(self, name="souffle", expect_size=1):
        self._name = name
        self._expect_size = expect_size

    def name(self):
        return self._name

    def solve(self, p, timeout=None, debug=False):
        with tempfile.NamedTemporaryFile(mode='w', delete=not debug) as temp:
            # Write the problem.
            with temp.file as f:
                self._write_program(p, out=f)

            # Invoke the solver.
            args = ["souffle", temp.name]
            result = benchmark_subprocess(args, timeout=timeout)

            assert result.process.returncode == 0
            assert result.process.stdout.decode() == f"{self.QUERY_NAME}\t{self._expect_size}\n"

            return result

    @classmethod
    def _write_program(cls, p, out):
        print('.decl node( a:symbol )', file=out)
        print('.decl edge( a:symbol, b:symbol )', file=out)
        print('.decl source( a:symbol )', file=out)
        print('.decl destination( a:symbol )', file=out)

        # Facts.
        write_connectivity_problem_facts(p, out=out)

        # Rules.
        print('.decl connected( a:symbol, b:symbol )', file=out)
        print('connected(A, B) :- edge(A, B).', file=out)
        print('connected(A, B) :- edge(A, M), connected(M, B).', file=out)

        # Query.
        print(f'.decl {cls.QUERY_NAME}( a:symbol, b:symbol )', file=out)
        print(f'.printsize {cls.QUERY_NAME}', file=out)
        print(f'{cls.QUERY_NAME}(S, D) :- source(S), destination(D), connected(S, D).', file=out)


def main(args):
    # Options.
    parser = argparse.ArgumentParser(
                        prog='benchmark',
                        description='Benchmark datalog solvers.')
    parser.add_argument('--root', default="../..", help="Path to veri-datalog repository root.")
    parser.add_argument('--results', default=sys.stdout, type=argparse.FileType('w'), help="Path to results CSV.")
    parser.add_argument('--nodes-min', default=3, type=int, help="Starting value for number of nodes.")
    parser.add_argument('--nodes-max', default=1000, type=int, help="Ending value for number of nodes.")
    parser.add_argument('--nodes-scale', default=1.23, type=float, help="Scale problem size by this factor.")
    parser.add_argument('--benchmarks-per-size', default=1, type=int, help="Number of problems per size.")
    parser.add_argument('--timeout', default=60, type=int, help="Timeout in seconds.")
    parser.add_argument('--log-level', default='info', type=str, help="Logging level.")
    parser.add_argument('--verbose', action='store_const', dest='log_level', const='debug', help="Verbose logging.")
    parser.add_argument('--debug', action='store_true', help="Debug mode.")

    opts = parser.parse_args(args)

    # Logging.
    log_level = 'debug' if opts.debug else opts.log_level
    logging.basicConfig(level=log_level.upper())

    logging.debug('options: %s', opts)

    # Solvers.
    solvers = [
        DafnySolver(
            "bottom-up",
            os.path.join(opts.root, "dafny", "bottom-up"),
            b"Query succeeded!"
        ),
        DafnySolver(
            "top-down",
            os.path.join(opts.root, "dafny", "top-down"),
            b"Query returned true"
        ),
        SouffleSolver(),
    ]
    for solver in solvers:
        logging.debug("configured solver: %s", solver.name())

    # TODO: "warmup" run (for example, in case dafny solvers not built)

    # Iterate over problem sizes.
    nodes = opts.nodes_min
    while nodes <= opts.nodes_max:
        for _ in range(opts.benchmarks_per_size):
            # Generate problem.
            p = random_connectivity_problem(nodes)
            problem_size = len(p.graph.nodes)
            logging.info("generated graph problem with %d nodes", problem_size)

            # Solve.
            w = csv.writer(opts.results)
            for solver in solvers:
                # Exec.
                logging.info("execute solver: %s", solver.name())
                try:
                    result = solver.solve(p, debug=opts.debug, timeout=opts.timeout)
                except subprocess.TimeoutExpired as error:
                    logging.warning("solver timeout after %d seconds", error.timeout)
                    continue

                # Record results.
                w.writerow([solver.name(), problem_size, result.elapsed_ns])
                opts.results.flush()

        # Advance to next node size.
        nodes = max(int(nodes * opts.nodes_scale), nodes+1)


if __name__ == "__main__":
    main(sys.argv[1:])
