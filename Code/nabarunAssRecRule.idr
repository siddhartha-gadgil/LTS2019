module AssRecRule

import Data.Fin
import Data.Vect

{-
 The recursion function for lists of type `a`. Define this by pattern matching
-}
recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x base step [] = base
recList a x base step (y :: ys) = step y ys (recList a x base step ys)

{-
Given a list of type `a` and a function `f: a -> b` get a list of type `b`
by applying `f` to each element.

Note: Define using `recList` and without pattern matching on lists.
-}
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f x = recList a (List b) [] step x where
  step = \y : a => \ys : List a => \result : List b => (f y) :: result

{-
Given a list of type `a`, an initial value `init: a` and an operation `op: a -> a -> a`,
get an element of `a` by starting with init and repeatedly applying the elements of the
list,
e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3

Note: Define using `recList` and without pattern matching on lists.
-}
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op y = recList a a init step y where
  step = \y : a => \ys : List a => \result : a => op y result

{-
The induction function on the `Fin` indexed type family. Define this by pattern matching.
-}
inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin _ _ _ Z FZ impossible
inducFin _ _ _ Z FS impossible
inducFin xs base step (S k) FZ = base k
inducFin xs base step (S k) (FS j) = step k j (inducFin xs base step k j)

{-
Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
get the element in position `j` of `v`. Note that this is always well defined.

Note: Define using `inducList` and without pattern matching on the `Fin` family. You may pattern match on Vectors.
The definition should have only one case, and there should be no case splitting on `Fin`
-}
fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a q j v = inducFin xs base step q j v where
  xs : (n : Nat) -> Fin n -> Type
  xs q j = Vect q a -> a
  base : (m : Nat) -> xs (S m) FZ
  base m = f where
    f (x :: xs) = x
  step : (p : Nat) -> (k : Fin p) -> (prev : xs p k) -> (xs (S p) (FS k))
  step p k prev (y :: ys) = prev ys
