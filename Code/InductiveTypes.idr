module InductiveTypes

import Data.Fin

%default total
%access public export

|||Type of inductive functions on lists
inducList : (a : Type) -> (xs : (List a -> Type)) -> (xs []) -> ((head : a) -> (tail : List a) -> (xs tail) -> (xs (head :: tail))) -> (lista : List a) -> (xs lista)
inducList a xs x0 f [] = x0
inducList a xs x0 f (head::lista) = f head lista (inducList a xs x0 f lista)

|||Type of recursive functions on lists
recList : (a : Type) ->  (x : Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)
recList a x x0 f list = inducList a (\list => x) x0 f list

|||Function that folds the values in a list
foldList : (a : Type) ->  (init : a) -> (op : a -> a -> a) -> List a -> a
foldList a a0 op lista = recList a a a0 (\a => (\lista => (\val => op a val))) lista

|||Function that maps a list of one type to a list of another type
mapList : (a: Type) -> (b: Type) -> (f: a -> b) -> List a -> List b
mapList a b f lista = recList a (List b) [] (\a => (\lista => (\listb => (f a)::listb))) lista

|||Type of inductive functions on Fin
inducFin : (xs : (n : Nat) -> Fin n -> Type) -> (base : ((m: Nat) -> xs (S m) FZ)) ->
		 (step : ((p : Nat) -> (k : Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k)))) ->
		 (q : Nat) -> (j : Fin q) -> (xs q j)
inducFin xs base step (S n) FZ = base n
inducFin xs base step (S n) (FS k) = step n k (inducFin xs base step n k)

|||Type of inductive functions on Nat
inducNat : (xs : (n : Nat) -> Type) -> (base : (xs Z)) ->
		 (step : ((n : Nat) -> (prev : (xs n)) -> (xs (S n)))) -> (n : Nat) -> (xs n)
inducNat xs base step Z = base
inducNat xs base step (S n) = step n (inducNat xs base step n)
