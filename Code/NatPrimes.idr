module NatPrimes

import InductiveTypes
import NatUtils
import NatOrder
import NatDivisors
import NatGCD

%default total
%access public export

----------------------------------------------------------------------------------------------

-- Definitions

|||A factorisation for a number
Factorisation : (n : Nat) -> Type
Factorisation n = (a : Nat ** (b : Nat ** ((LT 1 a, LT 1 b), n = a * b)))

|||Type of proof that a number is prime
isPrime : (p : Nat) -> Type
isPrime p = ((LT 1 p), {a : Nat} -> {b : Nat} -> (isDivisible (a * b) p) -> Either (isDivisible a p) (isDivisible b p))

|||Type of proof that a number is irreducible
isIrreducible : (p : Nat) -> Type
isIrreducible p = (a : Nat) -> (b : Nat) -> (p = a * b) -> Either (a = 1) (b = 1)

|||Type of proof that a number is the smallest divisor (greater than 1) of a given number
isMinDivisor : (n : Nat) -> (d : Nat) -> Type
isMinDivisor n d = ((LT 1 d), ((isDivisible n d), {k : Nat} -> (LT 1 k) -> (isDivisible n k) -> (LTE d k)))

-----------------------------------------------------------------------------------------------

--Basic Proofs

|||Proof that 1 < n implies n != 0
ltOneNotZ : {n : Nat} -> (LT 1 n) -> (Not (n = Z))
ltOneNotZ {n} ltProof = gtSuccImpliesNotZ n ltProof

|||Proof that p is irreducible and r < p, r ! = 0 implies r and p are coprime
remainderPrimeCoprime : {p : Nat} -> {r : Nat} ->
				    (isIrreducible p) -> (LNEQ r p) -> (Not (r = Z)) -> (coprime r p)
remainderPrimeCoprime {p} {r} proofIrreducible proofLNEQ rNotZ n (divr, (k ** (proofEq, notZ))) = case (proofIrreducible k n proofEq) of
	(Left kEq1) => void ((leqImpliesNotLNEQ (dividesImpliesGEQ (eqConservesDivisible divr Refl (sym (trans proofEq (trans (cong {f = (\a => a * n)} kEq1) (multOneLeftNeutral n))))) rNotZ)) proofLNEQ)
	(Right nEq1) => nEq1

|||Proof that if an irreducible does not divide a number, it is coprime to the number
irredNotDivIsCoprime : {p : Nat} -> (n : Nat) ->
				   (isIrreducible p) -> (Not (isDivisible n p)) -> (coprime n p)
irredNotDivIsCoprime {p} n proofIrreducible notDiv k (divRight, (l ** (proofEq, notZ))) =
	case (proofIrreducible l k proofEq) of
	(Left lEq1) => void (notDiv (eqConservesDivisible divRight Refl (sym (trans proofEq (trans (cong {f = (\a => a * k)} lEq1) (multOneLeftNeutral k))))))
	(Right kEq1) => kEq1

|||Proof that an irreducible either divides a number or is coprime to it
irreducibleDividesOrCoprime : {p : Nat} -> (n : Nat) -> (isIrreducible p) -> Either (isDivisible n p) (coprime n p)
irreducibleDividesOrCoprime {p} n proofIrreducible =
	case (decDivisible n p) of
		(Yes proofDiv) => (Left proofDiv)
		(No notDiv) => (Right (irredNotDivIsCoprime n proofIrreducible notDiv))

-----------------------------------------------------------------------------------------------

--Equivalence of irreducibility and primality in the naturals

|||Proof that a prime is irreducible
primeIsIrreducible : {p : Nat} -> (isPrime p) -> (isIrreducible p)
primeIsIrreducible {p} (proofLT, proofPrime) a b proofEq =
	case (proofPrime (1 ** ((rewrite (multOneLeftNeutral p) in (sym proofEq)), (ltOneNotZ proofLT)))) of
	(Left dividesA) =>
		case (dividesA) of
		(k ** (proofEq2, notZ)) => Right (sym (multLeftCancel p 1 b notZ (trans (rewrite (multOneRightNeutral p) in proofEq) (cong {f = (\n => n * b)} (multAntiSymmetric proofEq2 (trans proofEq (multCommutative a b)))))))
	(Right dividesB) =>
		case (dividesB) of
		(k ** (proofEq2, notZ)) => Left (sym (multRightCancel 1 a p notZ (trans (rewrite (multOneLeftNeutral p) in proofEq) (cong {f = (\n => a * n)} (multAntiSymmetric proofEq2 proofEq)))))

|||Proof that an irreducible greater than 1 is prime
irreducibleIsPrime : {p : Nat} -> (isIrreducible p) -> (LT 1 p) -> (isPrime p)
irreducibleIsPrime {p} proofIrreducible proofLT = (proofLT, proofPrime) where
	proofPrime : {a : Nat} -> {b : Nat} -> (isDivisible (a * b) p) -> Either (isDivisible a p) (isDivisible b p)
	proofPrime {a} {b} proofDiv =
		case (irreducibleDividesOrCoprime a proofIrreducible) of
		(Left divA) => (Left divA)
		(Right coprimeA) => (Right (coprimeImpliesDiv proofDiv coprimeA))

-----------------------------------------------------------------------------------------------

|||Proof that the smallest divisor is unique
minDivisorUnique : {n : Nat} -> {d1 : Nat} -> {d2 : Nat} ->
			    (isMinDivisor n d1) -> (isMinDivisor n d2) -> (d1 = d2)
minDivisorUnique {n} {d1} {d2} (ltLeft, (divLeft, minDivLeft)) (ltRight, (divRight, minDivRight)) = lteAntiSymmetric (minDivLeft ltRight divRight) (minDivRight ltLeft divLeft)

|||Proof that the smallest divisor of an irreducible is the irreducible itself
minDivOfIrreducible : {p : Nat} -> (LT 1 p) -> (isIrreducible p) -> (isMinDivisor p p)
minDivOfIrreducible {p} proofLT proofIrred = (proofLT, ((divisionReflexive (ltOneNotZ proofLT)), minDiv)) where
	minDiv : {n : Nat} -> (LT 1 n) -> (isDivisible p n) -> (LTE p n)
	minDiv {n} nLT1 (k ** (proofEq, notZ)) =
		case (proofIrred k n proofEq) of
		(Left kEq1) => lteSubstitutes lteRefl (sym (multOneLeftEqual proofEq kEq1)) Refl
		(Right nEq1) => void (succNotLTEzero (fromLteSucc (lteSubstitutes nLT1 Refl nEq1)))

----------------------------------------------------------------------------------------------
