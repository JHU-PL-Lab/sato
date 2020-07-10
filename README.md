Sato
=====

_"I am so embarrassed. My name's Asami. Let me make this up to you somehow. Uh...how about I treat you to dinner?"_ - Asami Sato, _The Legend of Korra_

**Sato**, the **S**ymbolic **A**nalysis **T**ypechecker for **O**defa, dynamically locates type errors during demand-driven symbolic execution.

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
- [] Write tests (most important)
 - [] Reorganize the rest of the pre-existing tests
 - [] All clause/expression types
 - [] Tests that condition control flow on input (Parallel type errors)
 - [] Serial type errors
 - [] Type error after infinite loop/omega combinator
 - [] Recursion
- [] Add "Primitive" pattern/type for bool + int "=="
- [] Change inputs
 - [] Remove #true# clauses
 - [x] DON'T add new types for inputs
- [] More errors
 - [] Match errors (conjunction vs. disjunction)
 - [] Divide by zero (new nonzero pattern?)
 - [] Asserts (encode in odefa)
- [] Add odefa-to-natodefa mapping
 - [] Variants, lists, and other advanced data structures
 - [] Line + column numbers
- [] Convert from nested clauses to "ANF" clauses (?)
 - [] Report first error/abort encountered; don't report subsequent errors
- [] Heuristic for when to end recursion
 - [] Idea 1: Scale max steps by lines of code
 - [] Idea 2: Limit context stack growth re. adding the same call site
- [] Report errors early, without having to reach the beginning (hard)
