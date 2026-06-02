# Planning in Lean

We define various concepts related to heuristic search for planning in this repo.
As the basis, we use the [formalisation of STRIPS planning by A. Nicodemos](https://github.com/AmosNico/validator) and the [implementation of graph search algorithms in Lean](https://github.com/galvusdamor/lean4-search-algorithms).

We defined the notion of heuristics for planning problems and created a planner based on it. We also provide implementations of the following heuristics and proved that they are admissible:

- the perfect heuristic h^*
- the perfect delete-relaxation heuristic h^+
- the maximum / critical path of width 1 heuristic h^1
- abstraction heuristics in general
- pattern database heuristics (PDBs)

We also proved that non-negative cost partitionings of admissible heuristics are again admissible.

## Running the Planner
This repo contains an executable, but practically very inefficient planner.
To run it, you first need to obtain the input file that our planner can read.
For that, you need [Downward Certificates](https://github.com/salome-eriksson/downward-certificates).
You **must** check out the certificates branch. It contains a file [CERTIFICATEs.md](>https://github.com/salome-eriksson/downward-certificates/blob/certificates/CERTIFICATES.md) which contains instruction on how to build the planner. The last version for which we verified that it is working correctly is [f5f3f7dd7975cf59bcd8de81836a43d9ebdbe96f](https://github.com/salome-eriksson/downward-certificates/commit/f5f3f7dd7975cf59bcd8de81836a43d9ebdbe96f).

You can obtain benchmark instances in either the [AI Basel](github.com/aibasel/downward-benchmarks/) or [Planning Community](https://github.com/AI-Planning/classical-domains) repositories.
Then run
```
./fast-downward.py PROBLEM.pddl --search "astar(hmax(),verify_optimality=true)"
```

This will create a file ``task.txt`` which is the grounded STRIPS version of the selected problem. You need this as input for the
planner. All other files can be discarded.

To run the planner, you first need to build it. For this run ``lake build``.

We recommend to run the planner executable directly as:
```
    .lake/build/bin/planner INPUT-FILE HEURISTIC
```
``INPUT-FILE`` is the ``task.txt`` file you obtained before. With ``HEURISTIC`` you may select the heuristic to be used. Currently, we only expose the constant zero heuristic ``h0`` and the maximum heuristic ``h1``.

The planner will then either output that no plan exists or that it found one and then print the plan in IPC (International Planning Competition) format.

Note that the planner is currently extremely inefficient when it comes to runtime. I.e. it is able to solve some small toy examples, but will fail so solve any reasonably large planning problem, usually because it will exhaust memory.

## Dependency Graph

![Dependency graph](dependencies.svg)

(Update this graph with `make dependencies.svg`.)
