module RecRule

import Data.Fin


% access public export


recNat : (x : Type) -> x -> (Nat -> x -> x) -> (Nat -> x)
recNat x base step Z = base
recNat x base step (S k) = step k (recNat x base step k)

fctl : Nat -> Nat
fctl = recNat Nat (S Z) step where
  step = \n: Nat => \y : Nat => (S n) * y

recListNat : (x: Type) -> x -> (Nat -> List Nat -> x -> x) -> (List Nat -> x)
recListNat x base step [] = base
recListNat x base step (y :: xs) = step y xs previous where
  previous = recListNat x base step xs

lsum : List Nat -> Nat
lsum = recListNat Nat base step where
  base = Z
  step = \h : Nat => \t : List Nat => \accum : Nat => h + accum

finToNat : (n: Nat) -> Fin(n) -> Nat
finToNat (S k) FZ = Z
finToNat (S k) (FS x) = S (finToNat k x)

recFin : (x: Type) ->
  (Nat -> x) ->
  ((n: Nat) -> Fin n -> x -> x) ->
  ((n: Nat) -> Fin n -> x)
recFin x base _ (S k) FZ = base k
recFin x base step (S k) (FS y) = step k y previous where
  previous = recFin x base step k y
