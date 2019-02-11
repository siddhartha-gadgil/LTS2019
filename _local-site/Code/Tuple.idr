module Tuple

Tup: Nat -> Type
Tup Z = Unit
Tup (S k) = (Nat, Tup k)

ct: (n: Nat) -> Tup n
ct Z = ()
ct (S k) = (S k, ct k)

bigId : (A : Type) -> A -> A
bigId = \A : Type => (\a : A => a)
