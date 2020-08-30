Sato
=====

_"I am so embarrassed. My name's Asami. Let me make this up to you somehow. Uh...how about I treat you to dinner?"_ - Asami Sato, _The Legend of Korra_

**Sato**, the **S**ymbolic **A**nalysis **T**ypechecker for **O**defa, dynamically locates type errors using demand-driven symbolic execution.

Install
-------

For Ubuntu install as follows.

```
sudo apt upgrade opam
opam update
opam switch create 4.09.0+flambda
```


Run this to produce libraries needed
```
# dune external-lib-deps --missing @@default
```

Here are the libraries needed:
```
opam install shexp core batteries gmap jhupllib monadlib ocaml-monadic pds-reachability ppx_deriving ppx_deriving_yojson -y
opam pin z3 4.8.1 -y
```

For Z3:
```
export LD_LIBRARY_PATH=`opam config var z3:lib`
```

Run
---

```
make
make test
make benchmark
```

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
- [ ] Write theory that maps errors in original code to aborts in instrumented code
  - [ ] Ignore errors in dead odefa code by throwing out aborts/errors encountered after the first one
- [ ] Write benchmarks
- [ ] Write library of commonly used predicates/contracts (copy from Clojure predicates?)

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
