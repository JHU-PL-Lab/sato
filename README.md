Sato
=====

_"I am so embarrassed. My name's Asami. Let me make this up to you somehow. Uh...how about I treat you to dinner?"_ - Asami Sato, _The Legend of Korra_

**Sato**, the **S**ymbolic **A**nalysis **T**ypechecker for **O**defa, dynamically locates type errors using demand-driven symbolic execution.

Install
-------

For MacOS, first install the requisite OCaml version: 4.09.0+flambda.
```
brew upgrade opam
opam update
opam switch create 4.09.0+flambda
```

(For Linux, replace `brew` with `apt get`.)

Run this to produce libraries needed
```
# dune external-lib-deps --missing @@default
```

Now we can install the dependencies for Sato.
```
opam install shexp core batteries gmap jhupllib monadlib ocaml-monadic pds-reachability ppx_deriving ppx_deriving_yojson -y
```

For Z3, we need to pin it to version 4.8.1 due to a bug with later versions; then we need to export the path Z3 is installed on:
```
opam pin z3 4.8.1 -y
export LD_LIBRARY_PATH=`opam config var z3:lib`
```

Run
---

To build Sato itself, run the `make` command (which is itself an alias for the `make sato` command); we can also run `make ddpa` and `make translator` in order to build other utilities which may be useful for debugging. The basic usage of Sato is as follows:
```
./sato <filename>
```
where `<filename>` refers to a `.odefa` or `.natodefa` file that Sato will typecheck.  For the full command list, run `./sato --help`.

To run tests on Sato (as well as DDPA and DDSE), run the `make test` command.

TODOs
---
- [x] Refactor codebase and fix bugs
  - [x] Write shared module type sig for odefa and natodefa errors
- [x] Formalize revised rules
  - [x] Add projection, match, and abort rules
  - [x] Formally incorporate alias-passing (ie. on a = b, return a instead of b)
  - [x] Fix bugs involving alias passing and non-singleton lookup stacks
- [ ] Continue to write tests
  - [x] Tests that exercise alias passing to test revised rules
  - [ ] More list tests (fold, sort, etc.)
- [x] Write theory that maps errors in original code to aborts in instrumented code
  - [x] Ignore errors in dead odefa code by throwing out aborts/errors encountered after the first one
- [x] Fix bugs relating to DDPA
  - Update: bugs revealed something fundamental to how lookup works; see below
- ~~Write benchmarks~~
- ~~Write library of commonly used predicates/contracts (copy from Clojure predicates?)~~

TODOs for theory refactor
----
- [x] Change abort syntax
  - [x] No enocding with lists: only one instrumentation conditional/predicate per abort
  - ~~Accumulate abort constraints at Conditional Bottom, not Abort~~
  - [x] Change pattern match encoding
  - [x] Change `==` encoding (if needed)
- ~~[ ] Add `nonzero` pattern (?)~~

TODOs for 100% coverage algorithm
----
- [x] Algorithm to discover all `abort` clauses
- [x] Record all visited aborts during lookup
- [x] Restart lookup until all aborts have been looked up/visited
  - [x] Deal with the "lookup starts off-by-one" problem
- [x] Write new tests for this
- [x] Note this in writeup

More TODOs
----
- [ ] Heuristic to identify higher-level errors (as opposed to strictly lower-level ones)
  - [ ] Incorrect data structures (e.g. using lists wrong)
  - [ ] Applying an incorrect variable to a function
- [ ] Add undefined value (replaces above bullet point)
- [x] Heuristic for when to end recursion
  - [ ] Idea 1: Scale max steps by lines of code
  - [ ] Idea 2: Limit context stack growth re. adding the same call site
  - [x] Actual solution: limit steps that each evaluation can take using the `--maximum-steps` arg
- [x] Report errors locally, without having to reach the beginning (hard)
  - [ ] Type errors after infinite loops/omega combinators
  - [ ] Type errors in non-satisfiable universes
  - [x] Actual solution: Perform "repeat evaluation on different vars" heuristic (see above)
- [x] Achieve 100% coverage in finding errors (ultimate goal...)
  - [ ] Run test from back, then if it gets stuck, restart in the middle of the program in a non-covered portion of code
  - [x] Tentatively achieved using heuristic...
  - \(This is a key advantage over forward analyses - no need to know values starting from the middle\)
