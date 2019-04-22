---
title: Recursion rules
date: 3 April 2019
---

In this assignment, you will work out some cases of using recursion and induction (including for indexed types) by:

* defining appropriate `rec` and `induc` functions by pattern matching in _Idris_
* after that, only using these, not direct pattern matching

The motivation for this is that `rec` and `induc` are cleanly defined, and any code in terms of these is correct (i.e., valid - it can of course still give the wrong results).

## Submission

Below is skeleton code for the assignment, also available on the [repository](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/AssRecRule.idr). To submit the assignment,

* create a file with this code with filename _[YourName]AssRecRule.idr_, e.g. _MickeyMouseAssRecRule.idr_
* fill in all the definitions, with pattern matching used to define `recList` and `inducFin`, but pattern matching for `List` and `Fin` not used after that (you can use pattern matching for vectors while defining `fetchElem`).
* e-mail the solution as a single file (with no dependencies) with subject _LTS2019 Assignment 2_ by the due date.

```idris
module AssRecRule

import Data.Fin
import Data.Vect

{-
 The recursion function for lists of type `a`. Define this by pattern matching
-}
recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)

{-
Given a list of type `a` and a function `f: a -> b` get a list of type `b`
by applying `f` to each element.
Note: Define using `recList` and without pattern matching on lists.
-}
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b

{-
Given a list of type `a`, an initial value `init: a` and an operation `op: a -> a -> a`,
get an element of `a` by starting with init and repeatedly applying the elements of the
list,
e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3
Note: Define using `recList` and without pattern matching on lists.
-}
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a


{-
The induction function on the `Fin` indexed type family. Define this by pattern matching.
-}
inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j


{-
Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
get the element in position `j` of `v`. Note that this is always well defined.

Note: Define using `inducList` and without pattern matching on the `Fin` family. You may pattern match on Vectors.
The definition should have only one case, and there should be no case splitting on `Fin`.
-}
fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
```
