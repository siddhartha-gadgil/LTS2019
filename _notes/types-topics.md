---
title: Type Theory topics
date: 2018-12-13
---

This is a list of the main topics, sometimes with corresponding examples, for the type theory we study.

- Recursive definitions: e.g. summing a list.
- First-class functions: e.g. `$\sum_{k=1}^{n} f(k)$`.
- Fibonacci numbers: indirect recursion
- Currying: Ackermann function (illustrates not only _primitve recursize_)
  - `A(0, n) = n + 1`
  - `A(m, 0) = A(m -1, 1)`
  - `A(m, n) = A(m - 1, A(m, n -1))`
- Type Families:
  - e.g. tuples
  - e.g. reversing tuples, including searching by type
- Propositions as types:
  - e.g. subtraction
  - propositional combinations
  - quantification
  - basic examples as inductive types
  - `Decidable` type; Collatz function
- Inductive types
  - e.g. trees, dependent pairs
  - `rec` and `induc` terms
- Indexed Inductive types
  - e.g. `Fin` type family
  - `induc` in the indexed case
- Equality type
  - path induction principle
  - groupoid operations and their logical counterparts.
