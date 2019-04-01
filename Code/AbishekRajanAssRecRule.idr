module AssRecRule

import Data.Fin
import Data.Vect

--Question 1
recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x base step [] = base
recList a x base step (z :: xs) = step z xs previous where
  previous = recList a x base step xs

--Question 2
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f xs = recList a (List b) base step xs where
  base = []
  step = \u: a => \r: List a => \d: List b => ((f u) :: d)

--Question 3 (this performs left folding, but the element init is evaluated at the end. I believe
--it is possible to perform the operation with 'init' at the beginning, but this would require the
-- the list to be reversed (which could be done with recList))
foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op xs = recList a a base step xs where
  base = init
  step = \u: a => \r: List a => \v: a => op u v

--Question 4
inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin xs base step (S k) FZ = base k
inducFin xs base step (S k) (FS x) = step k x previous where
  previous = inducFin xs base step k x

--Question 5
fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a q j vs = inducFin (mV a) base step q j vs where

  mV: (a: Type) -> (n: Nat) -> (q: Fin n) -> Type
  mV a n q = (Vect n a -> a)

  base: (m: Nat) -> (s: Vect (S m) a) -> a
  base m (x :: xs) = x

  step: (k: Nat) -> (q: Fin k) -> (f: Vect k a -> a) -> (Vect (S k) a) -> a
  step k q f (x :: xs) = f xs
