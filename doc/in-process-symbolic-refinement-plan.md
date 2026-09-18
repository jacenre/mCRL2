# In-Process Symbolic Refinement

## Goal

Run symbolic CEGAR approximations inside `pbescegps` instead of spawning a
`pbessolvesymbolic` process for every approximation. Keep Sylvan and Lace alive
for the whole CEGAR run, while releasing each approximation before solving the
next one.

## Current Constraint

Sylvan is process-global. The current child process isolates each call because
the symbolic state, Lace workers, and Sylvan tables are all created and quit
together.

The in-process design must therefore guarantee:

- one Lace/Sylvan runtime per CEGAR run;
- no live LDD handles from an old approximation when its state is released;
- both under- and over-approximation results remain queryable during refinement;
- cleanup on normal return and exceptions.

## Proposed Design

### Runtime Guard

Add an RAII runtime object responsible for:

1. `lace_start`;
2. Sylvan limits and package initialization;
3. LDD initialization;
4. `sylvan_quit` and `lace_stop`.

The guard is created once by `pbescegps` and destroyed after the CEGAR loop.
Nested guards are rejected or treated as no-ops.

### Symbolic Solver Object

Extract the solver flow currently in `pbessolvesymbolic.cpp` into a reusable
library object. It should own:

- the preprocessed SRF PBES;
- the reachability algorithm;
- the symbolic parity game;
- the symbolic solution and strategies;
- the data index and variable order needed to decode vertices.

The object should expose:

- the Boolean result;
- the winning region and strategy;
- initial-state access;
- successor queries for one symbolic vertex;
- strategy-successor queries;
- vertex decoding to a PVI.

### Approximation Lifetime

`pbescegps` should solve one approximation, use it for refinement, then destroy
that solver object before constructing the next approximation. This releases
the LDD roots. Sylvan itself stays initialized, so package startup is paid once.

The solution cache must either be removed or changed to hold solver objects only
when their LDD roots remain valid. A cache entry cannot outlive the runtime or
the data-index configuration it references.

## Refinement Adapter

Replace the eager `structure_graph` dependency with a symbolic adapter. The
existing refinement logic needs these operations:

- decode a vertex formula;
- find a matching vertex by common parameter values;
- get a strategy successor;
- test whether a specific edge exists;
- determine terminal decorations;
- enumerate successors when required by refinement.

The adapter should memoize only queried vertices and edges. It should not
enumerate the complete winning region.

The under- and over-approximation adapters use separate symbolic solver
objects. Their raw LDD indices must never be compared directly; matching remains
based on decoded PVI values and common parameters.

## Process Compatibility

Keep the current subprocess and serialized structure-graph path initially:

- it remains the fallback for evidence generation;
- it provides a reference implementation for result and refinement tests;
- it avoids changing all users at once.

Add an opt-in in-process mode first. The existing `--symbolic-structure-graph`
mode remains available until the adapter has equivalent coverage.

## Verification

Add tests for:

- repeated approximation solves under one Sylvan runtime;
- destruction and recreation of symbolic solver objects;
- exception cleanup of the runtime guard;
- matching refinement decisions against the subprocess path;
- equal final Boolean results;
- memory stability across many CEGAR iterations.

Run the existing `pbescegps` tests and the industrial CONT experiment in both
modes. Record approximation, refinement, Sylvan initialization, and cleanup
timings separately.

## Implementation Order

1. Extract and test the RAII runtime guard.
2. Extract the symbolic solver from the tool source into the PBES library.
3. Add explicit solver-object lifetime tests.
4. Implement lazy symbolic graph queries.
5. Adapt refinement to the query interface.
6. Add the in-process mode and retain subprocess fallback.
7. Compare results, decisions, timings, and memory use.
