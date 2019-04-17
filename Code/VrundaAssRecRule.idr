module AssRecRule

import Data.Fin
import Data.Vect

{-
 The recursion function for lists of type `a`. Define this by pattern matching
 recList : (x: Type) -> x -> (Nat -> List Nat -> x -> x) -> (List Nat -> x)
-}
recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x base step [] = base
recList a x base step (y :: xs) = step y xs (recList a x base step xs)

{-
Given a list of type `a` and a function `f: a -> b` get a list of type `b`
by applying `f` to each element.
Note: Define using `recList` and without pattern matching on lists.
-}
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f la = recList a (List b) [] step la where
  step = \y: a => \xs: List a => \listb: List b => (f y) :: listb
{-
Given a list of type `a`, an initial value `init: a` and an operation `op: a -> a -> a`,
get an element of `a` by starting with init and repeatedly applying the elements of the
list,
e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3
Note: Define using `recList` and without pattern matching on lists.
-}
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op la = recList a a init step la where
  step = \y: a => \xs: List a=> \prev : a => (op y prev)

{-
The induction function on the `Fin` indexed type family. Define this by pattern matching.
-}
inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin xs base step Z j = FinZElim j
inducFin xs base step (S p) FZ = base p
inducFin xs base step (S p) (FS k)  = step p k (inducFin xs base step p k)
{-
Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
get the element in position `j` of `v`. Note that this is always well defined.

Note: Define using `inducList` and without pattern matching on the `Fin` family. You may pattern match on Vectors.
The definition should have only one case, and there should be no case splitting on `Fin`.
-}
fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a q j vect =  inducFin xs base step q j vect where
  xs : (n: Nat) -> Fin n -> Type
  xs q j = Vect q a -> a
  base : (m: Nat) -> xs (S m) FZ
  base len = head
  step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))
  step p k prev = prevtail where
    prevtail : Vect (S p) a-> a
    prevtail (hd::tl) = prev tl
{-Q.E.D.-}
