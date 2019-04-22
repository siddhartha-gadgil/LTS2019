module gcd

import NatUtils
import NatOrder

%default total
%access public export

|||Auxilliary proof for euclidDivide
--Proof to finish euclidDivide, couldn't add it as a where clause within euclidDivide. If someone knows how to do that, please do so.
extendedEqualityProof : (a : Nat) -> (b : Nat) -> (q : Nat) -> (r : Nat)->
					((S r) = b) -> (a = r + (q * b)) -> (S a = (S q) * b)
extendedEqualityProof a b q r proofSmlEq proofBigEq =
	trans (cong proofBigEq) (plusConstantRight (S r) b (q * b) proofSmlEq)

||| Given a, b, and a proof that b != 0, returns (q, r) and proofs that a = bq + r, r < b
--removed possible problems with Rohit's
euclidDivide : (a : Nat) -> (b : Nat) -> (Not (b = Z)) ->
			(q : Nat ** (r : Nat ** (a = r + (q * b), LNEQ r b)))
euclidDivide _ Z proofeq = void(proofeq Refl)
euclidDivide Z (S k) SIsNotZ = (Z ** (Z ** (Refl, (LEQZero, ZIsNotS))))
euclidDivide (S n) (S k) SIsNotZ =
	case (euclidDivide n (S k) SIsNotZ) of
		(q ** (r ** (proofEq, proofLNEQ))) =>
			case (lneqImpliesEqOrLNEQ r (S k) proofLNEQ) of
				(Right proofSrLNEQSk) => (q ** ((S r) ** ((cong proofEq), proofSrLNEQSk)))
				(Left proofSrEqSk) => ((S q)** (Z ** ((extendedEqualityProof n (S k) q r proofSrEqSk proofEq), (LEQZero, ZIsNotS))))


||| Given a, b, and a proof that b != 0, returns (q, r) and proofs that a = bq + r, r < b (Old Version)
--removed possible problems with Rohit's
eculidDivideAux : (a : Nat) -> (b : Nat) ->
  (b = Z -> Void) -> (q : Nat ** (r : Nat ** ((a = r + (q * b)), LT r b)))
eculidDivideAux a b pf =
	let
		res = euclidDivide a b pf
		q = DPair.fst res
		r = DPair.fst (DPair.snd res)
		eqn = fst (DPair.snd (DPair.snd res))
		ltpf = lneqToLT (snd (DPair.snd (DPair.snd res)))
	in
		(q ** (r ** (eqn , ltpf)))

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

|||Type of proof that d is the GCD of a and b, where atleast one of a and b are non-zero
isGCD : (a : Nat) -> (b : Nat) -> Either (Not (a = Z)) (Not (b = Z)) -> (d : Nat) -> Type
isGCD a b notBothZ d = (dIsNotZ : Not (d = Z) ** ((isCommonDivisor a b d dIsNotZ), (n : Nat) -> (proofNotZ : Not (n = Z)) -> (isCommonDivisor a b n proofNotZ) -> (isDivisible d n proofNotZ)))

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
commonDivisorSymmetric : {a : Nat} -> {b : Nat} -> {d : Nat} -> {proofNotZ : Not (d = Z)} ->
					(isCommonDivisor a b d proofNotZ) -> (isCommonDivisor b a d proofNotZ)
commonDivisorSymmetric {a} {b} {d} (proofDividesa, proofDividesb) = (proofDividesb, proofDividesa)

|||Proof d divides a and a = b implies d divides b
eqConservesDivisible : {a : Nat} -> {b : Nat} -> {d : Nat} -> {proofNotZ : Not (d = Z)} ->
					(isDivisible a d proofNotZ) -> (a = b) -> (isDivisible b d proofNotZ)
eqConservesDivisible {a} {d} (n ** proofDivides) Refl = (n ** proofDivides)

|||Proof that d divides a implies d divides c * a
dividesMultiple : {a : Nat} -> {d : Nat} -> {proofNotZ : Not (d = Z)} ->
				(isDivisible a d proofNotZ) -> (c : Nat)-> (isDivisible (c * a) d proofNotZ)
dividesMultiple {d} (n ** Refl) c = ((c * n) ** (rewrite (multAssociative c n d) in Refl))

|||Proof that d is a common divisor of a and b implies d divides a + b
dividesSum :  {a : Nat} -> {b : Nat} -> {d : Nat} -> {proofNotZ : Not (d = Z)} ->
			(isCommonDivisor a b d proofNotZ)-> (isDivisible (a + b) d proofNotZ)
dividesSum {a} {b} {d} ((m ** proofDividesa), (n ** proofDividesb)) =
	((m + n) ** (distributeProof a b d m n proofDividesa proofDividesb))

|||Proof that d is a common divisor of a and b implies d divides a * x + b * y
dividesLinearCombination :  {a : Nat} -> {b : Nat} -> {d : Nat} -> {proofNotZ : Not (d = Z)} ->
						(isCommonDivisor a b d proofNotZ) -> (x : Nat) -> (y : Nat) ->
						(isDivisible ((x * a) + (y * b)) d proofNotZ)
dividesLinearCombination {proofNotZ = prf} commonDivisorProof x y =
	dividesSum {proofNotZ = prf} ((dividesMultiple {proofNotZ = prf} (fst commonDivisorProof) x), (dividesMultiple {proofNotZ = prf} (snd commonDivisorProof) y))

|||Proof that d divides n and n != 0 implies n >= d
dividesImpliesGEQ : {n : Nat} -> {d : Nat} -> {proofNotZ : Not (d = Z)} -> (isDivisible n d proofNotZ) -> (Not (n = Z)) -> (LEQ d n)
dividesImpliesGEQ {n} {d} {proofNotZ} (k ** proofEq) nNotZ =
	case k of
		Z => void (nNotZ proofEq)
		(S l) =>  ((l * d) ** (sym proofEq))

|||Proof that d divides (a + b) and d divides b implies d divides a
dividesDifference : {a : Nat} -> {b : Nat} -> {d : Nat} -> {proofNotZ : Not (d = Z)} -> (isDivisible (a + b) d proofNotZ) -> (isDivisible b d proofNotZ) -> (isDivisible a d proofNotZ)
dividesDifference {a} {b} {d} {proofNotZ} (n ** proofDivSum) (m ** proofDivb) =
	case (leqDivConstantRight proofNotZ (eqPreservesLEQ (a ** (plusCommutative b a)) proofDivb proofDivSum)) of
	(l ** proofEq) =>
		(l ** sym (plusLeftCancel b (l * d) a (rewrite (plusCommutative b a) in (rewrite proofDivSum in (rewrite proofDivb in (trans (sym (multDistributesOverPlusLeft m l d)) (cong {f = (\n => n * d)} proofEq)))))))

|||Proof that if n = r + q * d, where r ! = 0 and r < d,  then n is not divisible by d
notDivisible : {n : Nat} -> {r : Nat} -> {q : Nat} -> {d : Nat} -> (dNotZ : Not (d = Z)) ->
			(Not (r = Z)) -> (LNEQ r d) -> (n = r + (q * d)) -> (Not (isDivisible n d dNotZ))
notDivisible {n} {r} {q} {d} dNotZ rNotZ proofLNEQ proofEq (k ** proofDiv) =
	(leqImpliesNotLNEQ dLEQr proofLNEQ) where
		dLEQr = (dividesImpliesGEQ {proofNotZ = dNotZ} dDividesr rNotZ) where
			dDividesr = dividesDifference {proofNotZ = dNotZ} (k ** (trans (sym proofEq) proofDiv)) (q ** Refl)

|||Decision procedure to check if n is divisible by d
decDivisible : (n : Nat) -> (d : Nat) -> (proofNotZ : Not (d = Z)) -> Dec (isDivisible n d proofNotZ)
decDivisible n d proofNotZ = case (euclidDivide n d proofNotZ) of
	(q ** (r ** ((proofEq, proofLNEQ)))) =>
	case r of
		Z => Yes (q ** proofEq)
		(S k) => No (notDivisible proofNotZ SIsNotZ proofLNEQ proofEq)

|||Proof that d divides a, d divides b and a = r + q * b implies d divides r
dividesDiffExtend : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} -> {proofNotZ : Not (d = Z)} ->
 				(isDivisible a d proofNotZ) -> (isDivisible b d proofNotZ) -> (a = r + (q * b)) -> (isDivisible r d proofNotZ)
dividesDiffExtend {a} {b} {q} {r} {proofNotZ = dNotZ} dDividesa dDividesb proofEq =
	dividesDifference {proofNotZ = dNotZ} (eqConservesDivisible dDividesa proofEq) (dividesMultiple dDividesb q)

|||Returns the GCD of a and b with proof that it is the GCD
euclidGCD : (bound : Nat) -> (a : Nat) -> (b : Nat) -> (LTE a bound) -> (LTE (S b) bound) -> (notBothZ : (Either (Not (a = Z)) (Not (b = Z)))) -> (d : Nat ** (isGCD a b notBothZ d))
euclidGCD bound Z Z _ _ notBothZ = case notBothZ of
				Left notZ => void (notZ Refl)
				Right notZ => void (notZ Refl)
euclidGCD bound (S a) Z _ _ _ = ((S a) ** (SIsNotZ ** (zeroCommonDivisorRight, (\n : Nat => (\proofNotZ => (\proofCommonDivisor => (fst proofCommonDivisor)))))))
euclidGCD bound Z (S b) _ _ _ = ((S b) ** (SIsNotZ ** (zeroCommonDivisorLeft, (\n : Nat => (\proofNotZ => (\proofCommonDivisor => (snd proofCommonDivisor)))))))
euclidGCD Z (S a) (S b) lteLeft lteRight _ = void (succNotLTEzero lteLeft)
euclidGCD (S bound) (S a) (S b) (LTESucc lteLeft) (LTESucc lteRight) notBothZ =
	case (euclidDivide (S a) (S b) SIsNotZ) of
	(q ** (r ** (proofEq, proofLNEQ))) =>
		case (euclidGCD bound (S b) r lteRight (lteTransitive (lneqToLT proofLNEQ) lteRight) (Left SIsNotZ)) of
		(d ** (dNotZ ** (commonDivisorProof,  largestDivisorProof))) =>
			(d ** (dNotZ ** (((eqConservesDivisible {proofNotZ = dNotZ} (dividesSum {proofNotZ = dNotZ} ((snd commonDivisorProof), dividesMultiple {proofNotZ = dNotZ} (fst commonDivisorProof) q)) (sym proofEq)), (fst commonDivisorProof)), (\n => (\nNotZ => (\commonDivisor => (largestDivisorProof n nNotZ ((snd commonDivisor), (dividesDiffExtend {proofNotZ = nNotZ} (fst commonDivisor) (snd commonDivisor) proofEq)))))))))
