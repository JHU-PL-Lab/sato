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

To build Sato itself, we can run the `make sato` command; we can also run `make` in order to build Sato, DDSE, and the DDPA toploop, as well as a translator from Natodefa to Odefa.  The basic usage of Sato is as follows:
```
./type_checker -linfo -t<variable> <filename>
```
where `<filename>` refers to a `.odefa` or `.natodefa` file that Sato will typecheck, and `<variable>` is the variable that Sato begins symbolic lookup on.  For the full command list, run `./type_checker --help`.

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
- [ ] Fix bugs relating to DDPA
- [ ] Write benchmarks
- [ ] Write library of commonly used predicates/contracts (copy from Clojure predicates?)

TODOs for theory refactor
----
- [ ] Change abort syntax
  - [ ] No enocding with lists: only one instrumentation conditional/predicate per abort
  - [ ] Accumulate abort constraints at Conditional Bottom, not Abort
  - [x] Change pattern match encoding
  - [x] Change `==` encoding (if needed)
- Add `nonzero` pattern

More TODOs
----
- [ ] Heuristic to identify higher-level errors (as opposed to strictly lower-level ones)
  - [ ] Incorrect data structures (e.g. using lists wrong)
  - [ ] Applying an incorrect variable to a function
- [ ] Add undefined value (replaces above bullet point)
- [ ] Heuristic for when to end recursion
  - [ ] Idea 1: Scale max steps by lines of code
  - [ ] Idea 2: Limit context stack growth re. adding the same call site
- [ ] Report errors locally, without having to reach the beginning (hard)
  - [ ] Type errors after infinite loops/omega combinators
  - [ ] Type errors in non-satisfiable universes
- [ ] Achieve 100% coverage in finding errors (ultimate goal...)
  - [ ] Run test from back, then if it gets stuck, restart in the middle of the program in a non-covered portion of code
  - \(This is a key advantage over forward analyses - no need to know values starting from the middle\)
