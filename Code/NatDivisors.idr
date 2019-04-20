module NatDivisors

import NatUtils
import NatOrder

%default total
%access public export

---------------------------------------------------------------------------------------------

--Definitions involving divisibility

|||Type of proof that d divides n
isDivisible : (n : Nat) -> (d : Nat) -> Type
isDivisible n d = (k : Nat ** (n = k * d, Not (d = Z)))

|||Type of proof that d is a common divisor of a and b
isCommonDivisor : (a : Nat) -> (b : Nat) -> (d : Nat) -> Type
isCommonDivisor a b d = (isDivisible a d, isDivisible b d)

|||Type of proof that a given number is "larger" than all common divisors of a and b
isMaxDivisor : (a : Nat) -> (b : Nat) -> (d : Nat) -> Type
isMaxDivisor a b d = (n : Nat) -> (isCommonDivisor a b n) -> (isDivisible d n)

---------------------------------------------------------------------------------------------

-- Division algorithms to get the quotient and reminder

||| Given a, b, and a proof that b != 0, returns q, r and proofs that a = r + (b * q) and  r < b (r < b as LT r b)
--removed possible problems with Rohit's
euclidDivideOld : (a : Nat) -> (b : Nat) -> (Not (b = Z)) ->
			   (q : Nat ** (r : Nat ** ((a = r + (q * b)), LT r b)))
euclidDivideOld _ Z proofEq = void (proofEq Refl)
euclidDivideOld Z (S k) SIsNotZ = (Z ** (Z ** (Refl, LTESucc LTEZero)))
euclidDivideOld (S n) (S k) SIsNotZ =
	case (euclidDivideOld n (S k) SIsNotZ) of
	(q ** (r ** (proofEq, ltproof))) =>
		case (ltImpliesEqOrLT r (S k) ltproof) of
		(Right proofSrLTSk) => (q ** ((S r) ** ((cong proofEq), proofSrLTSk)))
		(Left proofSrEqSk) => ((S q) ** (Z ** ((trans (cong proofEq) (plusConstantRight (S r) (S k) (q * (S k)) proofSrEqSk)), LTESucc LTEZero)))

||| Given a, b, and a proof that b != 0, returns (q, r) and proofs that a = r + q * b and r < b (r < b as LNEQ r b)
euclidDivide : (a : Nat) -> (b : Nat) -> (Not (b = Z)) ->
			(q : Nat ** (r : Nat ** (a = r + (q * b), LNEQ r b)))
euclidDivide _ Z proofeq = void (proofeq Refl)
euclidDivide Z (S k) SIsNotZ = (Z ** (Z ** (Refl, (LEQZero, ZIsNotS))))
euclidDivide (S n) (S k) SIsNotZ =
	case (euclidDivide n (S k) SIsNotZ) of
		(q ** (r ** (proofEq, proofLNEQ))) =>
			case (lneqImpliesEqOrLNEQ r (S k) proofLNEQ) of
				(Right proofSrLNEQSk) => (q ** ((S r) ** ((cong proofEq), proofSrLNEQSk)))
				(Left proofSrEqSk) => ((S q) ** (Z ** ((trans (cong proofEq) (plusConstantRight (S r) (S k) (q * (S k)) proofSrEqSk)), (LEQZero, ZIsNotS))))

---------------------------------------------------------------------------------------------

-- General recursive functions for proofs using Euclid's division algorithms

|||A general algorithm that runs recursively using Euclid's division, with proof (helper function with bound, use euclidRecursion instead)
euclidRecursionBound : (bound : Nat) -> (a : Nat) -> (b : Nat) -> (LTE a bound) -> (LTE (S b) bound) -> (Either (Not (a = Z)) (Not (b = Z))) ->
(proofType : (Nat -> Nat -> Type)) ->
(baseLeft : (k : Nat) -> (Not (k = Z)) -> (proofType k Z)) ->
(baseRight : (k : Nat) -> (Not (k = Z)) -> (proofType Z k)) ->
(proofExtend : {a1 : Nat} -> {b1 : Nat} -> {r1 : Nat} -> {q1 : Nat} -> (proofType b1 r1) -> (a1 = r1 + (q1 * b1)) -> (proofType a1 b1)) ->
(proofType a b)

euclidRecursionBound _ Z Z _ _ notBothZ _ _ _ _ =
	case notBothZ of
		Left notZ => void (notZ Refl)
		Right notZ => void (notZ Refl)

euclidRecursionBound bound (S a) Z _ _ _ _ baseLeft _ _ = baseLeft (S a) SIsNotZ
euclidRecursionBound bound Z (S b) _ _ _ _ _ baseRight _ = baseRight (S b) SIsNotZ

euclidRecursionBound Z (S a) (S b) lteLeft lteRight _ _ _ _ _ = void (succNotLTEzero lteLeft)

euclidRecursionBound (S bound) (S a) (S b) (LTESucc lteLeft) (LTESucc lteRight) _
proofType baseLeft baseRight proofExtend =
	case (euclidDivide (S a) (S b) SIsNotZ) of
		(q ** (r ** (proofEq, proofLNEQ))) =>
			case (euclidRecursionBound bound (S b) r lteRight (lteTransitive (lneqToLT proofLNEQ) lteRight) (Left SIsNotZ) proofType baseLeft baseRight proofExtend) of
				proofRemainder => proofExtend proofRemainder proofEq



|||A general algorithm that runs recursively using Euclid's division, with proof
euclidRecursion : (a : Nat) -> (b : Nat) -> (Either (Not (a = Z)) (Not (b = Z))) ->
(proofType : (Nat -> Nat -> Type)) ->
(baseLeft : (k : Nat) -> (Not (k = Z)) -> (proofType k Z)) ->
(baseRight : (k : Nat) -> (Not (k = Z)) -> (proofType Z k)) ->
(proofExtend : {a1 : Nat} -> {b1 : Nat} -> {r1 : Nat} -> {q1 : Nat} -> (proofType b1 r1) -> (a1 = r1 + (q1 * b1)) -> (proofType a1 b1)) ->
(proofType a b)

euclidRecursion a b notBothZ proofType baseLeft baseRight proofExtend =
	case (isLTE a b) of
		(Yes proofLTE) => euclidRecursionBound (S b) a b (lteTransitive proofLTE (lteSuccRight lteRefl)) lteRefl notBothZ proofType baseLeft baseRight proofExtend
		(No proofNotLTE) => euclidRecursionBound (S a) a b (lteSuccRight lteRefl) (LTESucc (notLTEImpliesGTE proofNotLTE)) notBothZ proofType baseLeft baseRight proofExtend

----------------------------------------------------------------------------------------------

--Basic utility functions involving divisibility

|||Proof d1 divides a1 and a1 = a2, d1 = d2 implies d2 divides a2
eqConservesDivisible : {a1 : Nat} -> {a2 : Nat} -> {d1 : Nat} -> {d2 : Nat} ->
				   (isDivisible a1 d1) -> (a1 = a2) -> (d1 = d2) -> (isDivisible a2 d2)
eqConservesDivisible {a1} {d1} proofDivides Refl Refl = proofDivides

|||Proof that all natural numbers divide zero
zeroDivisible : {n : Nat} -> (Not (n = Z)) -> (isDivisible Z n)
zeroDivisible {n} notZ = (Z ** (sym (multZeroLeftZero n), notZ))

|||Proof that 1 divides all natural numbers
oneDivides : {n : Nat} -> (isDivisible n (S Z))
oneDivides {n} = (n ** ((rewrite (multOneRightNeutral n) in Refl), SIsNotZ))

|||Proof that all natural numbers divide themselves
divisionReflexive : {n : Nat} -> (Not (n = Z)) -> (isDivisible n n)
divisionReflexive {n} notZ = (1 ** (rewrite (multOneLeftNeutral n) in Refl, notZ))

|||Proof that 1 is a common divisor of all pairs of natural numbers
oneCommonDivisor : {a : Nat} -> {b : Nat} -> (isCommonDivisor a b (S Z))
oneCommonDivisor {a} {b} = (oneDivides, oneDivides)

|||Proof that n is a common divisor of n and 0
zeroCommonDivisorRight : {n : Nat} -> (Not (n = Z)) -> (isCommonDivisor n Z n)
zeroCommonDivisorRight {n} notZ = (divisionReflexive notZ, zeroDivisible notZ)

|||Proof that n is a common divisor of 0 and n
zeroCommonDivisorLeft : {n : Nat} -> (Not (n = Z)) -> (isCommonDivisor Z n n)
zeroCommonDivisorLeft {n} notZ = (zeroDivisible notZ, divisionReflexive notZ)

|||Proof that a common divisor of (a, b) is a common divisor of (b, a)
commonDivisorSymmetric : {a : Nat} -> {b : Nat} -> {d : Nat} ->
					(isCommonDivisor a b d) -> (isCommonDivisor b a d)
commonDivisorSymmetric {a} {b} {d} (proofDividesa, proofDividesb) =
	(proofDividesb, proofDividesa)

|||Proof that a divides b and b divides a implies a = b
dividesAntiSymmetric : {a : Nat} -> {b : Nat} ->
				   (isDivisible a b) -> (isDivisible b a) -> (a = b)
dividesAntiSymmetric {a} {b} (k ** (leftEq, leftNotZ)) (l ** (rightEq, rightNotZ)) =
	multAntiSymmetric leftEq rightEq

----------------------------------------------------------------------------------------------

--Utility functions for linear combinations

|||Proof that d divides a implies d divides n * a
dividesMultiple : {a : Nat} -> {d : Nat} ->
			   (isDivisible a d) -> (n : Nat) -> (isDivisible (n * a) d)
dividesMultiple {a} {d} (k ** (proofDiv, notZ)) n = ((n * k) ** (proofEq, notZ)) where
	proofEq = rewrite (sym (multAssociative n k d)) in
			cong {f = (\l => n * l)} proofDiv

|||Proof that a divides n and b divides (n/a) implies b * a divides n
multipleDivides : {n : Nat} -> {a : Nat} -> {b : Nat} -> (proofDiv : isDivisible n a) ->
			   (isDivisible (fst proofDiv) b) -> (isDivisible n (b * a))
multipleDivides {n} {a} {b} (k ** (proofDiv1, aNotZ)) (l ** (proofDiv2, bNotZ)) =
	(l ** (proofEq, nonZeroMultNotZero bNotZ aNotZ)) where
		proofEq = rewrite (multAssociative l b a) in
				rewrite (sym proofDiv2) in proofDiv1

|||Proof that d divides a and n != 0 implies (n * d) divides (n * a)
multipleDividesMultiple : {a : Nat} -> {d : Nat} -> (isDivisible a d) ->
					 (n : Nat) -> (Not (n = Z)) -> (isDivisible (n * a) (n * d))
multipleDividesMultiple {a} {d} (k ** (proofDiv, dNotZ)) n nNotZ =
	(k ** (proofEqExtend, (nonZeroMultNotZero nNotZ dNotZ))) where
		proofEqExtend = rewrite (multAssociative k n d) in
					 rewrite (multCommutative k n) in
					 rewrite (sym (multAssociative n k d)) in
					 cong {f = (\l => (n * l))} proofDiv

|||Proof that d is a common divisor of a and b implies d divides a + b
dividesSum : {a : Nat} -> {b : Nat} -> {d : Nat} ->
		   (isCommonDivisor a b d)-> (isDivisible (a + b) d)
dividesSum {a} {b} {d} ((m ** (proofDividesa, dNotZ1)), (n ** (proofDividesb, dNotZ2))) =
	((m + n) ** ((distributeProof a b d m n proofDividesa proofDividesb), dNotZ1))

|||Proof that d is a common divisor of a and b implies d divides x * a + y * b
dividesLinearCombination : {a : Nat} -> {b : Nat} -> {d : Nat} ->
					  (isCommonDivisor a b d) -> (x : Nat) -> (y : Nat) ->
					  (isDivisible ((x * a) + (y * b)) d)
dividesLinearCombination commonDivisorProof x y =
	dividesSum ((dividesMultiple (fst commonDivisorProof) x), (dividesMultiple (snd commonDivisorProof) y))

|||Proof that d divides (a + b) and d divides b implies d divides a
dividesDifference : {a : Nat} -> {b : Nat} -> {d : Nat} ->
				(isDivisible (a + b) d) -> (isDivisible b d) -> (isDivisible a d)
dividesDifference {a} {b} {d} (n ** (proofDivSum, dNotZ1)) (m ** (proofDivb, dNotZ2)) =
	case (leqDivConstantRight dNotZ1 (eqPreservesLEQ (a ** (plusCommutative b a)) proofDivb proofDivSum)) of
	(l ** proofEq) =>
		(l ** (sym (plusLeftCancel b (l * d) a (rewrite (plusCommutative b a) in (rewrite proofDivSum in (rewrite proofDivb in (trans (sym (multDistributesOverPlusLeft m l d)) (cong {f = (\n => n * d)} proofEq)))))), dNotZ1))

|||Proof that d divides b, d divides r and a = r + q * b implies d divides a
dividesSumExtend : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} ->
			    (isDivisible b d) -> (isDivisible r d) -> (a = r + (q * b)) ->
			    (isDivisible a d)
dividesSumExtend {a} {b} {q} {r} divB divR proofEq =
	(eqConservesDivisible (dividesSum (divR, dividesMultiple divB q)) (sym proofEq) Refl)

|||Proof that d divides a, d divides b and a = r + q * b implies d divides r
dividesDiffExtend : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} ->
				(isDivisible a d) -> (isDivisible b d) -> (a = r + (q * b)) -> (isDivisible r d)
dividesDiffExtend {a} {b} {q} {r} divA divB proofEq =
	dividesDifference (eqConservesDivisible divA proofEq Refl) (dividesMultiple divB q)

----------------------------------------------------------------------------------------------

-- Proofs involving divisibility with remainders

|||Proof that given a = r + q * b, and d divides b and r, d divides a and b
remExtendsCommDiv : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} -> {d : Nat} ->
				(isCommonDivisor b r d) -> (a = r + (q * b)) -> (isCommonDivisor a b d)
remExtendsCommDiv {a} {b} {q} {r} (divB, divR) proofEq = (divA, divB) where
	divA = dividesSumExtend divB divR proofEq

|||Proof that given a = r + q * b, and d divides a and b, d divides b and r
remConservesCommDiv : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} -> {d : Nat} ->
				  (isCommonDivisor a b d) -> (a = r + (q * b)) -> (isCommonDivisor b r d)
remConservesCommDiv {a} {b} {q} {r} (divA, divB) proofEq = (divB, divR) where
	divR = dividesDiffExtend divA divB proofEq

|||Proof that given a = r + q * b, and d divides a and b, d divides b and r
remExtendsMaxDiv : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} -> {d : Nat} ->
			    (isMaxDivisor b r d) -> (a = r + (q * b)) -> (isMaxDivisor a b d)
remExtendsMaxDiv maxDiv proofEq =
	(\n => (\commDiv => maxDiv n (remConservesCommDiv commDiv proofEq)))

|||Proof that given a = r + q * b, and d divides b and r, d divides a and b
remConservesMaxDiv : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} -> {d : Nat} ->
				 (isMaxDivisor a b d) -> (a = r + (q * b)) -> (isMaxDivisor b r d)
remConservesMaxDiv maxDiv proofEq =
	(\n => (\commDiv => maxDiv n (remExtendsCommDiv commDiv proofEq)))

----------------------------------------------------------------------------------------------

--Decidability of divisibility

|||Proof that d divides n and n != 0 implies n >= d
dividesImpliesGEQ : {n : Nat} -> {d : Nat} -> (isDivisible n d) -> (Not (n = Z)) -> (LEQ d n)
dividesImpliesGEQ {n} {d} (k ** (proofEq, dNotZ)) nNotZ =
	case k of
		Z => void (nNotZ proofEq)
		(S l) =>  ((l * d) ** (sym proofEq))

|||Proof that if n = r + q * d, where r ! = 0 and r < d,  then n is not divisible by d
notDivisible : {n : Nat} -> {r : Nat} -> {q : Nat} -> {d : Nat} ->
			(Not (r = Z)) -> (LNEQ r d) -> (n = r + (q * d)) -> (Not (isDivisible n d))
notDivisible {n} {r} {q} {d} rNotZ proofLNEQ proofEq (k ** (proofDiv, dNotZ)) =
	(leqImpliesNotLNEQ dLEQr proofLNEQ) where
		dLEQr = (dividesImpliesGEQ dDividesr rNotZ) where
			dDividesr = dividesDifference (k ** ((trans (sym proofEq) proofDiv), dNotZ)) (q ** (Refl, dNotZ))

|||Decision procedure to check if n is divisible by d
decDivisible : (n : Nat) -> (d : Nat) -> Dec (isDivisible n d)
decDivisible n Z = No (\proofDivides => (snd (snd proofDivides)) Refl)
decDivisible n (S d) =
	case (euclidDivide n (S d) SIsNotZ) of
		(q ** (r ** ((proofEq, proofLNEQ)))) =>
			case r of
				Z => Yes (q ** (proofEq, SIsNotZ))
				(S k) => No (notDivisible SIsNotZ proofLNEQ proofEq)

----------------------------------------------------------------------------------------------
