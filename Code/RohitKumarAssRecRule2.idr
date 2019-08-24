module AssRecRule

import Data.Fin
import Data.Vect

{-
 The recursion function for lists of type `a`. Define this by pattern matching
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
mapList a b f x = recList a (List b) [] step2 x where
  step2 : a -> List a -> List b -> List b
  step2 a1 y1 z1 = (f a1) :: z1

{-
Given a list of type `a`, an initial value `init: a` and an operation `op: a -> a -> a`,
get an element of `a` by starting with init and repeatedly applying the elements of the
list,
e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3
Note: Define using `recList` and without pattern matching on lists.
-}
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op y = recList a a init step3 y where
  step3 : a -> List a -> a -> a
  step3 a1 la1 a2 = op a2 a1

{-
The induction function on the `Fin` indexed type family. Define this by pattern matching.
-}
inducFin : (xs : (n: Nat) -> Fin n -> Type) -> (base : (m: Nat) -> xs (S m) FZ) -> (step : (p: Nat) -> (k: Fin p) -> (prev: xs p k) -> (xs (S p) (FS k))) -> (q: Nat) -> (j: Fin q) -> xs q j
inducFin xs base step (S q) FZ = base q
inducFin xs base step (S q) (FS x) = step q x (inducFin xs base step q x)

{-
Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
get the element in position `j` of `v`. Note that this is always well defined.

Note: Define using `inducList` and without pattern matching on the `Fin` family. You may pattern match on Vectors.
The definition should have only one case, and there should be no case splitting on `Fin`.
-}
fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a q j = inducFin xs base step q j where
  xs : (n: Nat) -> Fin n -> Type
  xs n m = (Vect n a -> a)
  base : (m: Nat) -> xs (S m) FZ
  base m = basef where
    basef : (Vect (S m) a) -> a
    basef (x :: y) = x
  step : (p: Nat) -> (k: Fin p) -> (prev: xs p k) -> (xs (S p) (FS k))
  step p k prev = stepf where
    stepf : (Vect (S p) a) -> a
    stepf (x :: y) = prev y
