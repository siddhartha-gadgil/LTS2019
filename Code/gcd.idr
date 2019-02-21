module gcd

import NatUtils

||| Given a, b, and a proof that b != 0, returns (q, r) and proofs that a = bq + r, r < b
--removed possible problems with Rohit's
euclidDivide : (a : Nat) -> (b : Nat) -> (b = Z -> Void) -> (r : Nat ** (q : Nat ** ((a = r + (q * b)), LT r b)))
euclidDivide _ Z proofeq = void(proofeq Refl)
euclidDivide Z (S k) SIsNotZ = (Z ** (Z ** (Refl, LTESucc LTEZero)))
euclidDivide (S n) (S k) SIsNotZ =
	case (euclidDivide n (S k) SIsNotZ) of
		(r ** (q ** (equalityProof, ltproof))) =>
			case (proofLTimplieseqorLT r (S k) ltproof) of
				(Right proofSrLTSk) => ((S r) ** (q ** ((functionExtendsEquality Nat S n (r + (q * (S k))) equalityProof), proofSrLTSk)))
				(Left proofSreqSk) => (Z ** ((S q) ** ((extendedEqualityProof n (S k) q r proofSreqSk equalityProof), LTESucc LTEZero)))

|||Type of proof that d divides a
isDivisible : (a : Nat) -> (d : Nat) -> (Not (d = Z)) -> Type
isDivisible a d proofNotZ = (n : Nat ** a = n * d)

|||Proof that all natural numbers divide zero
zeroDivisible : {n : Nat} ->  isDivisible Z (S n) SIsNotZ
zeroDivisible {n} = (Z ** sym (multZeroLeftZero (S n)))

|||Proof that 1 divides all natural numbers
oneDivides : {n : Nat} -> isDivisible n (S Z) SIsNotZ
oneDivides {n} = (n ** rewrite multOneRightNeutral n in Refl)

|||Proof that all natural numbers divide themselves
divisionReflexive : {n : Nat} -> (isDivisible (S n) (S n) SIsNotZ)
divisionReflexive {n} = (S Z ** rewrite multOneLeftNeutral n in Refl)

|||Type of proof that d is a common divisor of a and b
isCommonDivisor : (a : Nat) -> (b : Nat) -> (d : Nat) -> (Not (d = Z)) -> Type
isCommonDivisor a b d proofNotZ = (isDivisible a d proofNotZ, isDivisible b d proofNotZ)

|||Proof that 1 is a common divisor of all pairs of natural numbers
oneCommonDivisor : {a : Nat} -> (b : Nat) -> (isCommonDivisor a b (S Z) SIsNotZ)
oneCommonDivisor {a} {b} = (oneDivides, oneDivides)

|||Proof that n is a common divisor of n and 0
zeroCommonDivisorRight : {n : Nat} -> (isCommonDivisor (S n) Z (S n) SIsNotZ)
zeroCommonDivisorRight {n} = (divisionReflexive, zeroDivisible)

|||Proof that n is a common divisor of 0 and n
zeroCommonDivisorLeft : {n : Nat} -> (isCommonDivisor Z (S n) (S n) SIsNotZ)
zeroCommonDivisorLeft {n} = (zeroDivisible, divisionReflexive)

|||Proof that a common divisor of (a, b) is a common divisor of (b, a)
commonDivisorSymmetric : {a : Nat} -> {b : Nat} -> {d : Nat} -> (isCommonDivisor a b d proofNotZ) -> (isCommonDivisor b a d proofNotZ)
commonDivisorSymmetric {a} {b} {d} (proofDividesa, proofDividesb) = (proofDividesb, proofDividesa)

|||Proof that d divides a implies d divides c * a
dividesMultiple : {a : Nat} -> {d : Nat} -> (isDivisible a d proofNotZ) -> (c : Nat)-> (isDivisible (c * a) d proofNotZ)
dividesMultiple {d} (n ** Refl) c = ((c * n) ** (rewrite (multAssociative c n d) in Refl))

|||Proof of distributivity
distributeProof: (a : Nat) -> (b : Nat) -> (d : Nat) -> (m : Nat) -> (n : Nat) ->
(a = m * d) -> (b = n * d) -> ((a + b) = (m + n) * d)
distributeProof a b d m n proofDividesa proofDividesb =
	rewrite (multDistributesOverPlusLeft m n d) in
		(trans (the (a + b = (m * d) + b) (v1)) v2) where
			v1 = plusConstantRight a (m * d) b proofDividesa
			v2 = plusConstantLeft b (n * d) (m * d) proofDividesb

|||Proof that d is a common divisor of a and b implies d divides a + b
dividesSum :  {a : Nat} -> {b : Nat} -> {d : Nat} -> (isCommonDivisor a b d proofNotZ)-> (isDivisible (a + b) d proofNotZ)
dividesSum {a} {b} {d} ((m ** proofDividesa), (n ** proofDividesb)) =
	((m + n) ** (distributeProof a b d m n proofDividesa proofDividesb))
