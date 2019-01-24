module Bezout

data IsaDivisor : Nat -> Nat -> Type where
  OneDiv : (m : Nat) -> IsaDivisor 1 m
  MulDiv : (n : Nat) -> IsaDivisor 1 m -> IsaDivisor n (n*m)

--Examples
twoDivEight : IsaDivisor 2 8
twoDivEight = MulDiv 2 (OneDiv 4)

--GCD for a and b
grcd : (a : Nat) -> (b : Nat) -> Nat
grcd a b = if (b == Z) then a else (grcd b (modNat a b))
