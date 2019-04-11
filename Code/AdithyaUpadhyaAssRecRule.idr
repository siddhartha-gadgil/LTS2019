module AssRecRule

import Data.Fin
import Data.Vect

%default total

{-
 The recursion function for lists of type `a`. Define this by pattern matching
-}
recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x x0 f [] = x0
recList a x x0 f (head::lista) = f head lista (recList a x x0 f lista)
{-
Given a list of type `a` and a function `f: a -> b` get a list of type `b`
by applying `f` to each element.
Note: Define using `recList` and without pattern matching on lists.
-}
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f lista = recList a (List b) [] (\a => (\lista => (\listb => (f a)::listb))) lista

{-
Given a list of type `a`, an initial value `init: a` and an operation `op: a -> a -> a`,
get an element of `a` by starting with init and repeatedly applying the elements of the
list,
e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3
Note: Define using `recList` and without pattern matching on lists.
-}
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a a0 op lista = recList a a a0 (\a => (\lista => (\val => op a val))) lista

{-
The induction function on the `Fin` indexed type family. Define this by pattern matching.
-}
inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin xs base step (S n) FZ = base n
inducFin xs base step (S n) (FS k) = step n k (inducFin xs base step n k)

{-
Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
get the element in position `j` of `v`. Note that this is always well defined.
Note: Define using `inducList` and without pattern matching on the `Fin` family. You may pattern match on Vectors.
-}

fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a q j v = (inducFin xs base step q j) v where
	xs : (n: Nat) -> Fin n -> Type
	xs n k = (Vect n a -> a)
	base : (m: Nat) -> xs (S m) FZ
	base m (x :: v) = x
	step :  (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))
	step p k prev (x :: v) = prev v
