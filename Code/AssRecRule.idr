module AssRecRule

import Data.Fin
import Data.Vect

% access public export



recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x base step [] = base
recList a x base step (y :: xs) = step y xs previous where
  previous = recList a x base step xs

mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f = recList a (List b) base step where
  base = []
  step head tail prev = (f head) :: prev

foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op = recList a a base step where
  base = init
  step head tail prev = op head prev


recFin : (x: Type) ->
  (Nat -> x) ->
  ((n: Nat) -> Fin n -> x -> x) ->
  ((n: Nat) -> Fin n -> x)
recFin x base _ (S k) FZ = base k
recFin x base step (S k) (FS y) = step k y previous where
  previous = recFin x base step k y

inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin xs base step (S l) FZ = base l
inducFin xs base step (S l) (FS x) =
  step l x prev where
    prev = inducFin xs base step l x

fetchFamily: (a: Type) -> (n: Nat) -> Fin n -> Type
fetchFamily a n x = ((Vect n a) -> a)

fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a  = inducFin (fetchFamily a) base step where
  base m (x :: xs) =  x
  step p k prev (x :: xs) =
    fetchElem a p k xs
