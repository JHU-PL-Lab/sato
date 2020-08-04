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

TODO
---
- [x] Write tests (most important)
  - [x] Reorganize the rest of the pre-existing tests
  - [x] All clause/expression types
  - [x] Tests that condition control flow on input (Parallel type errors)
  - [x] Serial type errors
  - [x] Type error after infinite loop/omega combinator
  - [x] Recursion
- [x] Add "no type errors found" message if there are no type errors
- [ ] More precise type errors
  - [x] ~~For knock-on type errors, chain them together using abort information and report number~~
  - [x] ~~Report actual knock-on errors instead of the count?~~
  - [x] No need to report (unreachable) knock-on errors
  - [ ] If incorrectly-typed var was a function argument, report call site instead of original definition
  - [x] Report original binop instead of new constrained binop as value source (at least for odefa)
- [x] Refactor the solver
  - [x] ~~Replace separate `symbol_type` with `type_sig`~~ (Added comments instead)
  - [x] Add Input to values
- [x] Change inputs
  - [x] Remove #true# clauses
  - [x] Add appropriate variant type for input values
  - [x] DON'T add new types for inputs
- [x] Fix bug where record projection errors are not caught
  - [x] Idea - introduce value of type Bottom to AST/Abstract AST
- [x] Encode aborts with the relevant conditional identifiers
  - [x] Check to ensure that conditionals are valid (ie. are nested and include the abort as the final retv), either before or during lookup.
  - [x] Extract predicate and use constraint set to extract patterns + boolean operators
  - [ ] Continue to refine predicate tree construction
  - [x] Extract return values; retvs from true branches are what the abort constrains
- [ ] Report potential errors that may arise in dead code
  - [ ] Prove the soundness of reporting such potential errors
- [ ] More errors
  - [ ] ~~Add "Primitive" pattern/type for bool + int "=="~~ Use an `or` statement instead
  - [ ] Divide by zero (new nonzero pattern + type vs. nested constraints) - refinement types!
  - [ ] Match errors (conjunction vs. disjunction)
  - [ ] Asserts (including fancier types/predicates) (encode in odefa)
- [x] Deal with aborts in the (regular) interpreter environment
- [ ] Heuristic to identify higher-level errors (as opposed to strictly lower-level ones)
  - [ ] Incorrect data structures (e.g. using lists wrong)
  - [ ] Applying an incorrect variable to a function
- [ ] Add undefined value (replaces above bullet point)
- [ ] Add odefa-to-natodefa mapping
  - [ ] Variants, lists, and other advanced data structures
  - [ ] Line + column numbers
- [x] Convert from nested clauses to "ANF" clauses
  - [x] Report first error/abort encountered; don't report subsequent errors
- [ ] Heuristic for when to end recursion
  - [ ] Idea 1: Scale max steps by lines of code
  - [ ] Idea 2: Limit context stack growth re. adding the same call site
- [ ] Report errors locally, without having to reach the beginning (hard)
  - [ ] Type errors after infinite loops/omega combinators
  - [ ] Type errors in non-satisfiable universes
- [ ] Achieve 100% coverage in finding errors (ultimate goal...)
  - [ ] Run test from back, then if it gets stuck, restart in the middle of the program in a non-covered portion of code
  - [x] \(This is a key advantage over forward analyses - no need to know values starting from the middle\)
