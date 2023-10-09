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


class SouffleSolverBase(Solver):
    def __init__(self, expect_size=1):
        self._expect_size = expect_size

    def solve(self, p, timeout=None, debug=False):
        with tempfile.NamedTemporaryFile(mode='w', delete=not debug) as temp:
            # Write the problem.
            with temp.file as f:
                self._write_program(p, out=f)

            # Invoke the solver.
            result = self._invoke(p, temp.name, timeout=timeout, debug=debug)

            assert result.process.returncode == 0
            assert result.process.stdout.decode() == f"{self.QUERY_NAME}\t{self._expect_size}\n"

            return result

    @abstractmethod
    def _invoke(self, p, filename, timeout=None, debug=False):
        raise NotImplementedError()

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


class SouffleSolver(SouffleSolverBase):
    def name(self):
        return "souffle"

    def _invoke(self, p, filename, timeout=None, debug=False):
        args = ["souffle", filename]
        return benchmark_subprocess(args, timeout=timeout)


class SouffleSolverProvenance(SouffleSolverBase):
    def name(self):
        return "souffle-provenance"

    def _invoke(self, p, filename, timeout=None, debug=False):
        with tempfile.NamedTemporaryFile(mode='w', delete=not debug) as provenance:
            # Build input to the interactive explain session.
            proof_depth = 10*len(p.graph.nodes)

            explain_input = "format json\n"
            explain_input += f"output {provenance.name}\n"
            explain_input += f"setdepth {proof_depth}\n"
            explain_input += f'explain query("{p.src}", "{p.dst}")\n'
            explain_input += "quit\n"

            # Execute.
            args = ["souffle", "-t", "explain", filename]
            result = benchmark_subprocess(args, timeout=timeout, input=explain_input.encode())

            # Verify the provenance file was written to.
            assert os.path.exists(provenance.name)
            provenance_size = os.path.getsize(provenance.name)
            assert provenance_size > 0

            logging.debug('provenance output: file %s size %d bytes', provenance.name, provenance_size)

            return result


class SWISolver(Solver):
    GOAL = "go"

    def __init__(self, name="swi"):
        self._name = name

    def name(self):
        return self._name

    def solve(self, p, timeout=None, debug=False):
        with tempfile.NamedTemporaryFile(mode='w', delete=not debug) as temp:
            # Write the problem.
            with temp.file as f:
                self._write_datalog(p, out=f)

            # Invoke the solver.
            args = ["swipl", "-l", temp.name, "-g", self.GOAL, "-g", "halt"]
            result =  benchmark_subprocess(args, timeout=timeout)

            assert result.process.returncode == 0
            assert result.process.stdout.decode() == f"{p.src}{p.dst}\n"

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

        # Top-level.
        print(f'{cls.GOAL} :- forall(once({cls.QUERY_NAME}(S, D)), (write(S), write(D), nl)).', file=out)


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
        SouffleSolverProvenance(),
        SWISolver(),
    ]
    for solver in solvers:
        logging.debug("configured solver: %s", solver.name())

    # TODO: "warmup" run (for example, in case dafny solvers not built)

    # Iterate over problem sizes.
    nodes = opts.nodes_min
    disabled = set()
    while nodes <= opts.nodes_max:
        for _ in range(opts.benchmarks_per_size):
            # Generate problem.
            p = random_connectivity_problem(nodes)
            problem_size = len(p.graph.nodes)
            logging.info("generated graph problem with %d nodes", problem_size)

            # Solve.
            w = csv.writer(opts.results)
            for solver in solvers:
                if solver.name() in disabled:
                    logging.debug("skipping solver: %s", solver.name())
                    continue

                # Exec.
                logging.info("execute solver: %s", solver.name())
                try:
                    result = solver.solve(p, debug=opts.debug, timeout=opts.timeout)
                except subprocess.TimeoutExpired as error:
                    logging.warning("solver timeout after %d seconds: disabling", error.timeout)
                    disabled.add(solver.name())
                    continue

                # Record results.
                w.writerow([solver.name(), problem_size, result.elapsed_ns])
                opts.results.flush()

        # Advance to next node size.
        nodes = max(int(nodes * opts.nodes_scale), nodes+1)


if __name__ == "__main__":
    main(sys.argv[1:])
