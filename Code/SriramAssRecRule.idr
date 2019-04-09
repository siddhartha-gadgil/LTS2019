module AssRecRule

import Data.Fin
import Data.Vect

%default total
%access public export

recList : (a: Type) ->  (x: Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x base fn [] = base
recList a x base fn (y :: xs) = fn y xs (recList a x base fn xs)

mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f lst = recList a (List b) []
      (\q => \lsta => \lstb => (f q) :: lstb) lst

foldList : (a: Type) ->  (init: a) -> (op : a -> a -> a) -> List a -> a
foldList a init op xs = recList a a init (\q => \lst => op q) xs

inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j
inducFin xs base step (S k) FZ = base k
inducFin xs base step (S k) (FS x) = step k x (inducFin xs base step k x)

fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)
fetchElem a q j vect = inducFin (\n => \q => Vect n a -> a)
                       (\m => \(x :: xs) => x)
                       (\p => \k => \prev => \(x :: xs) => prev xs)
                       q j vect
