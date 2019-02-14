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

-- proof that a given number is prime
isPrime : Nat -> Type
isPrime p = ?needstobefilled

--proof that n is composite
Factorise : Nat -> Type
Factorise n = ?dsf

-- Given a number, either it is prime or it is composite
NPrimeOrComposite : Nat -> Either (isPrime n) (Factorise n)
NPrimeOrComposite n = ?fill
