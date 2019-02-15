module Primes
import NatUtils

%access public export

--isDivisible a b can be constucted if b divides a
isDivisible : Nat -> Nat -> Type
isDivisible a b = (n : Nat ** a = b * n)

--1 divides everything
oneDiv : (a : Nat) -> isDivisible a 1
oneDiv a = (a ** rewrite plusZeroRightNeutral a in Refl)

--If 1|a => 1*c | a*c
mulDiv : (a, c : Nat) -> isDivisible a 1 -> isDivisible (a * c) c
mulDiv a c x = (a ** rewrite multCommutative a c in Refl)

--Type for isPrime. A number p is prime if all numbers dividing
--it are either p or 1. (In the primality checker, I am checking
--for numbers until p, hence the p case is not included. Will
--be changed in a future update.)
isPrime : Nat -> Type
isPrime p = (LTE 2 p ,
            (x : Nat **
            (isDivisible p x , x = 1)))

--Either(a=b)(_) <=> Either (S a = S b)(_)
help1 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT (S a) (S b)) (LT (S b) (S a))) ->
  Either (S a = S b) (Either (LT (S a) (S b)) (LT (S b) (S a)))
help1 {a} {b} (Left l) = Left (eqSucc a b l)
help1 (Right r) = Right r

--Either(_)(Either(Sa<Sb)(_)) <=> Either (_)(Either(a<b)(_))
help2 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT a b) (LT (S b) (S a))) ->
  Either (a = b) (Either (LT (S a) (S b)) (LT (S b) (S a)))
help2 (Left l) = Left l
help2 {a} {b} (Right (Left l)) = Right(Left (LTESucc l))
help2 (Right (Right r)) = Right (Right r)

--Either(_)(Either(_)(Sb<Sa)) <=> Either (_)(Either(_)(b<a))
help3 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT a b) (LT b a)) ->
  Either (a = b) (Either (LT a b) (LT (S b) (S a)))
help3 (Left l) = Left l
help3 (Right (Left l)) = Right(Left l)
help3 {a} {b} (Right (Right r)) = Right (Right (LTESucc r))

|||Either a = b, a < b, or a > b
totOrdNat : (a : Nat) -> (b : Nat) ->
  Either (a = b) (Either (LT a b) (LT b a))
totOrdNat Z Z = Left Refl
totOrdNat Z (S k) = Right (Left (LTESucc LTEZero))
totOrdNat (S k) Z = Right (Right (LTESucc LTEZero))
totOrdNat (S k) (S j) = help1 (help2 (help3 (totOrdNat k j)))


--Does the job, but is not very useful. Will be replaced later.
checkPrime : (p : Nat) -> LTE 2 p -> {default (p-1) iter : Nat} ->
  Maybe (isPrime p)
checkPrime p pf {iter=Z} = Nothing
checkPrime p pf {iter=(S Z)} = Just (pf, ((S Z) ** (oneDiv p, Refl)))
checkPrime p pf {iter=(S k)} = case modNatNZ p (S k) SIsNotZ of
                            Z => Nothing
                            (S m) => checkPrime p pf {iter=k}
