module Primes

--isDivisible a b can be constucted if b divides a
isDivisible : Nat -> Nat -> Type
isDivisible a b = (n : Nat ** a = b * n)

--1 divides everything
oneDiv : (a : Nat) -> isDivisible a 1
oneDiv a = (a ** rewrite plusZeroRightNeutral a in Refl)

--If 1|a => 1*c | a*c
mulDiv : (a, c : Nat) -> isDivisible a 1 -> isDivisible (a * c) c
mulDiv a c x = (a ** rewrite multCommutative a c in Refl)

isPrime : Nat -> Type
isPrime p = GT p 1 -> (x : Nat) ->  modNatNZ p x -> Either (x = 1) (x = p))

checkPrime : (p : Nat) -> (iter : Nat) -> Either (sisPrime p) (isPrime p -> Void)
checkPrime p Z = ?df_1
checkPrime p (S k) = ?df_2


--p is a Prime is x|p => x=1 or x=p
data IsPrime : (p : Nat) -> Type where
  MkPrime : GT p 1 ->
            ((x : Nat) -> isDivisible p x -> Either (x = 1) (x = p)) ->
            IsPrime p
