--sandbox primes
module sandBoxPrime

import sandboxInductiveTypes
import sandboxNatUtils
import sandboxGCD
import sandboxNatOrder
import sandboxNatDivisors

%default total
%access public export

-------------------------------------------------------------------------------

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
primeIsIrreducible : {p : Nat} -> (isPrime p) -> (a : Nat) -> (b : Nat) -> (p = a * b) -> Either (a = 1) (b = 1)
primeIsIrreducible {p} (proofLT, proofPrime) a b proofEq =
	case (proofPrime (1 ** ((rewrite (multOneLeftNeutral p) in (sym proofEq)), (gtSuccImpliesNotZ p proofLT)))) of
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

|||Returns the smallest divisor (greater than 1) of a number with proof that it is the smallest factor
minDivisor : (n : Nat) -> (LT 1 n) -> (d : Nat ** isMinDivisor n d)
--minDivisor Z proofLT = void (succNotLTEzero proofLT)
--minDivisor (S Z) (LTESucc proofLT) = void (succNotLTEzero proofLT)
--minDivisor (S (S k)) _ =

minDivisorIsPrime : {n : Nat} -> {d : Nat} -> (isMinDivisor n d) -> (isPrime d)

|||Given a number n and a proof that 1 < n, returns whether it is prime or composite
decPrime : (n : Nat) -> (LT 1 n) -> Either (Factorisation n) (isPrime n)


--|||A list of the prime factors of a number with their multiplicities
--primeFactorisation : (n : Nat) -> ((primeFactors : (List (((p : Nat) ** (isPrime p))))) ** (n = (foldList Nat 1 (*) (mapList ((p : Nat) ** (isPrime p)) Nat (\element => (fst element)) primeFactors))))
