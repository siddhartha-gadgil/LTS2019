module Tuple

import Data.Fin

Tup: Nat -> Type
Tup Z = Unit
Tup (S k) = (Nat, Tup k)

ct: (n: Nat) -> Tup n
ct Z = ()
ct (S k) = (S k, ct k)

bigId : (A : Type) -> A -> A
bigId = \A : Type => (\a : A => a)

data Tree : Type  where
  TLeaf : Nat -> Tree
  TNode : (n: Nat) -> Fin n -> Tree

data Evil: Type where
  Diag : (Evil -> Bool) -> Evil

evil: Evil -> Bool
evil (Diag f) = not (f (Diag f))
