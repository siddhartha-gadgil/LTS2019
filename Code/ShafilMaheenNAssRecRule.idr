
module AssRecRule

import Data.Fin
import Data.Vect
%default total
%access public export

{-
 The recursion function for lists of type `a`. Define this by pattern matching
-}
recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x base step [] = base
recList a x base step (y :: xs) = (step y xs previous) where
  previous = recList a x base step xs

{-
Given a list of type `a` and a function `f: a -> b` get a list of type `b`
by applying `f` to each element.
Note: Define using `recList` and without pattern matching on lists.
-}
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f = recList a (List b) [] step where
  step = \y:a => \xs:(List a)  => \blist:(List b) => (f(y)::blist)

{-
Given a list of type `a`, an initial value `init: a` and an operation `op: a -> a -> a`,
get an element of `a` by starting with init and repeatedly applying the elements of the
list,
e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3
Note: Define using `recList` and without pattern matching on lists.
-}

|||The way I have defined foldList, if init =p and list is [q,r], it will return
|||op((op(p,r)),q).
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op = recList a a init step where
  step = \y:a => \xs:(List a) => \previous:a => (op previous y)



{-
The induction function on the `Fin` indexed type family. Define this by pattern matching.
-}
inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin xs base step (S k) FZ = base  k
inducFin xs base step (S k) (FS x) = step k x (inducFin xs base step k x)


{-
Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
get the element in position `j` of `v`. Note that this is always well defined.

Note: Define using `inducList` and without pattern matching on the `Fin` family. You may pattern match on Vectors.
The definition should have only one case, and there should be no case splitting on `Fin`.
-}

|||Specifies the output type for fetchelem
outTypeFetchElem: (a:Type) ->(n:Nat) -> Fin n -> Type
outTypeFetchElem a n x = (Vect n a ->a)


baseFetchElem : (m : Nat) -> Vect (S m) a -> a
baseFetchElem m (x :: xs) = x

stepFetchElem : (p : Nat) -> Fin p -> (Vect p a -> a) -> Vect (S p) a -> a
stepFetchElem p x f (y :: xs) = f (xs)

fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a   = inducFin (outTypeFetchElem a) baseFetchElem stepFetchElem
