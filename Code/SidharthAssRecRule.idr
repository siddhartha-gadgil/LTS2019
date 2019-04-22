module AssRecRule

import Data.Fin
import Data.Vect

{-
 The recursion function for lists of type `a`. Define this by pattern matching
-}
recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x emp fn [] = emp
recList a x emp fn (head :: ls) = fn head ls (recList a x emp fn ls)

{-
Given a list of type `a` and a function `f: a -> b` get a list of type `b`
by applying `f` to each element.
Note: Define using `recList` and without pattern matching on lists.
-}
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f ls = recList a (List b) [] map ls where
  map head la lb = (f head) :: lb

{-
Given a list of type `a`, an initial value `init: a` and an operation `op: a -> a -> a`,
get an element of `a` by starting with init and repeatedly applying the elements of the
list,
e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3
Note: Define using `recList` and without pattern matching on lists.
-}
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op ls = recList a a init map ls where
  map head la val = op head val

{-
The induction function on the `Fin` indexed type family. Define this by pattern matching.
-}
inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin _ _ _ Z FZ impossible
inducFin _ _ _ Z (FS _) impossible
inducFin xs base step (S k) FZ = base k
inducFin xs base step (S k) (FS x) = step k x (inducFin xs base step k x)


{-
Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
get the element in position `j` of `v`. Note that this is always well defined.

Note: Define using `inducList` and without pattern matching on the `Fin` family. You may pattern match on Vectors.
The definition should have only one case, and there should be no case splitting on `Fin`.
-}
fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a q j ys = inducFin xs base step q j ys where
  xs: (n: Nat) -> Fin n -> Type
  xs n j = Vect n a -> a
  base m = retHead where
    retHead: Vect (S m) a -> a --retrieve Head
    retHead (x :: ls) = x
  step p k prev = retStep where --reduce list to smaller one
    retStep : Vect (S p) a -> a
    retStep (x :: ls) = prev ls
