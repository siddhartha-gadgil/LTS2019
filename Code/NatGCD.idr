module NatGCD

import NatUtils
import NatOrder
import NatDivisors

%default total
%access public export

----------------------------------------------------------------------------------------------

-- Definitions

|||Type of proof that d is the GCD of a and b, where atleast one of a and b are non-zero
isGCD : (a : Nat) -> (b : Nat) -> (g : Nat) -> Type
isGCD a b g = ((isCommonDivisor a b g), (isMaxDivisor a b g))

|||Type that stores the GCD of two numbers
gcd : (a : Nat) -> (b : Nat) -> Type
gcd a b = (d : Nat ** (isGCD a b d))

|||Type of proof that a and b are coprime
coprime : (a : Nat) -> (b : Nat) -> Type
coprime a b = ((n : Nat) -> (isCommonDivisor a b n) -> (n = 1))

----------------------------------------------------------------------------------------------

--Basic proofs involving GCDs and coprime numbers

|||Proof that if a1 = a2, b1 = b2 then gcd (a1, b1) = gcd (a2, b2)
eqConservesGCD : {a1 : Nat} -> {b1 : Nat} -> {g1 : Nat} ->
			  {a2 : Nat} -> {b2 : Nat} -> {g2 : Nat} ->
			  (a1 = a2) -> (b1 = b2) -> (g1 = g2) ->
			  (isGCD a1 b1 g1) -> (isGCD a2 b2 g2)
eqConservesGCD {a1} {b1} {g1} Refl Refl Refl proofGCD = proofGCD

|||Proof that if a1 = a2, b1 = b2 and a1 and b1 are coprime, a2 and b2 are coprime
eqConservesCoprime : {a1 : Nat} -> {b1 : Nat} -> {a2 : Nat} -> {b2 : Nat} ->
				 (a1 = a2) -> (b1 = b2) -> (coprime a1 b1) -> (coprime a2 b2)
eqConservesCoprime {a1} {b1} Refl Refl proofCoprime = proofCoprime

|||Proof that the gcd is unique
gcdUnique : {a : Nat} -> {b : Nat} ->
		  (gcd1 : (gcd a b)) -> (gcd2 : (gcd a b)) -> ((fst gcd1) = (fst gcd2))
gcdUnique {a} {b} (g1 ** (commDiv1, maxDiv1)) (g2 ** (commDiv2, maxDiv2)) = dividesAntiSymmetric (maxDiv1 g2 commDiv2) (maxDiv2 g1 commDiv1)

|||Proof that gcd is symmetric
gcdSymmetric : {a : Nat} -> {b : Nat} -> {g : Nat} -> (isGCD a b g) -> (isGCD b a g)
gcdSymmetric {a} {b} {g} (commonDiv, maxDiv) = (commonDivisorSymmetric commonDiv, (\n => (\commDiv => (maxDiv n (commonDivisorSymmetric commDiv)))))

|||Proof that coprimality is symmetric
coprimeSymmetric : {a : Nat} -> {b : Nat} -> (coprime a b) -> (coprime b a)
coprimeSymmetric {a} {b} proofCoprime =
	(\n => (\commDiv => (proofCoprime n (commonDivisorSymmetric commDiv))))

|||Proof that gcd (a, b) = 1 implies a and b are coprime
gcdOneImpliesCoprime : {a : Nat} -> {b : Nat} -> (isGCD a b 1) -> (coprime a b)
gcdOneImpliesCoprime {a} {b} (commonDivisor, maxDivisor) =
	(\n => (\commonDiv => dividesAntiSymmetric oneDivides (maxDivisor n commonDiv)))

|||Proof that gcd (a, b) exists implies that both a and b are not zero
gcdImpliesNotBothZ : {a : Nat} -> {b : Nat} -> {g : Nat} ->
				 (isGCD a b g) -> Either (Not (a = Z)) (Not (b = Z))
gcdImpliesNotBothZ {a = Z} {b = Z} {g} (commonDiv, maxDiv) =
	void ((lneqImpliesNotLEQ (ltToLNEQ lteRefl)) (dividesImpliesGEQ (maxDiv (S g) (zeroDivisible SIsNotZ, zeroDivisible SIsNotZ)) (snd (snd (fst commonDiv)))))
gcdImpliesNotBothZ {a = (S k)} {b} {g} _ = (Left SIsNotZ)
gcdImpliesNotBothZ {a} {b = (S l)} {g} _ = (Right SIsNotZ)

|||Proof that a and b are coprime implies gcd (a, b) = 1
coprimeImpliesGCDOne : {a : Nat} -> {b : Nat} -> (coprime a b) -> (isGCD a b 1)
coprimeImpliesGCDOne {a} {b} proofCoprime = (oneCommonDivisor, (\n => (\commonDiv => eqConservesDivisible oneDivides Refl (sym (proofCoprime n commonDiv)))))

|||Proof that given g = gcd (a, b), 1 = gcd(a/g, b/g)
divImpliesGCDOne : {a : Nat} -> {b : Nat} -> {g : Nat} -> (proofGCD : isGCD a b g) ->
			    (isGCD (fst (fst (fst proofGCD))) (fst (snd (fst proofGCD))) 1)
divImpliesGCDOne {a} {b} {g} ((divLeft1, divRight1), maxDiv) =
	coprimeImpliesGCDOne proofCoprime where
		proofCoprime : (coprime (fst divLeft1) (fst divRight1))
		proofCoprime n (divLeft2, divRight2) = (multLeftIdIsOne (snd (snd divLeft1)) (dividesAntiSymmetric (dividesMultiple (divisionReflexive (snd (snd divLeft1))) n) (maxDiv (n * g) (multipleDivides divLeft1 divLeft2, multipleDivides divRight1 divRight2))))

|||Generates gcd (a, Z) given a and a proof that a != 0
gcdRightZero : (a : Nat) -> (Not (a = Z)) -> (gcd a Z)
gcdRightZero a notZ = (a ** ((zeroCommonDivisorRight notZ, (\n => (\proofCommonDivisor => (fst proofCommonDivisor))))))

|||Generates gcd (Z, b) given b and a proof that b != 0
gcdLeftZero : (b : Nat) -> (Not (b = Z)) -> (gcd Z b)
gcdLeftZero b notZ = (b ** (zeroCommonDivisorLeft notZ, (\n => (\proofCommonDivisor => (snd proofCommonDivisor)))))

|||Proof that gcd (a, Z) = a
gcdRightZeroRefl : (a : Nat) -> (proofGCD : (gcd a Z)) -> (a = (fst proofGCD))
gcdRightZeroRefl a (g ** ((divA, divZ), maxDiv)) =
	case (gcdImpliesNotBothZ ((divA, divZ), maxDiv)) of
		(Left notZ) => dividesAntiSymmetric divA (maxDiv a ((divisionReflexive notZ), (zeroDivisible notZ)))
		(Right notZ) => void (notZ Refl)

|||Proof that gcd (Z, b) = b
gcdLeftZeroRefl : (b : Nat) -> (proofGCD : (gcd Z b)) -> (b = (fst proofGCD))
gcdLeftZeroRefl b (g ** ((divZ, divB), maxDiv)) =
	case (gcdImpliesNotBothZ ((divZ, divB), maxDiv)) of
		(Left notZ) => void (notZ Refl)
		(Right notZ) => dividesAntiSymmetric divB (maxDiv b ((zeroDivisible notZ), (divisionReflexive notZ)))

----------------------------------------------------------------------------------------------

--Proofs used in Euclid's division algorithm for the GCD

|||Proof that given gcd (b, r) = g, a = r + q * b, and b ! = 0, gcd (a, b) = g
remainderExtendsGCD : {a : Nat} -> {b : Nat} -> {g : Nat} -> {r : Nat} -> {q : Nat} ->
				  (isGCD b r g) -> (a = r + (q * b)) -> (isGCD a b g)
remainderExtendsGCD {a} {b} {g} {r} {q} (commDiv, maxDiv) proofEq =
	(remExtendsCommDiv commDiv proofEq, remExtendsMaxDiv maxDiv proofEq)

|||Proof that given gcd (a, b) = g, a = r + q * b, and b ! = 0, gcd (b, r) = g
remainderConservesGCD : {a : Nat} -> {b : Nat} -> {g : Nat} -> {r : Nat} -> {q : Nat} ->
				    (isGCD a b g) -> (a = r + (q * b)) -> (isGCD b r g)
remainderConservesGCD {a} {b} {g} {r} {q} (commDiv, maxDiv) proofEq =
	(remConservesCommDiv commDiv proofEq, remConservesMaxDiv maxDiv proofEq)

----------------------------------------------------------------------------------------------

-- Euclid's algorithm for the GCD of two numbers

|||Returns gcd (a, b) with proof that it is the gcd
euclidGCD : (a : Nat) -> (b : Nat) -> (Either (Not (a = Z)) (Not (b = Z))) -> (gcd a b)
euclidGCD a b notBothZ =
	euclidRecursion a b notBothZ (\a => (\b => (gcd a b))) gcdRightZero gcdLeftZero (\proofGCD => (\proofEq => ((fst proofGCD) ** remainderExtendsGCD (snd proofGCD) proofEq)))

|||Returns gcd (a, b) with proof that it is the gcd and an auxilliary proof
euclidGCDExtend : (a : Nat) -> (b : Nat) -> (Either (Not (a = Z)) (Not (b = Z))) ->
(proofType : (Nat -> Nat -> Nat -> Type)) ->
(baseLeft : (k : Nat) -> (Not (k = Z)) -> (proofType k Z k)) ->
(baseRight : (k : Nat) -> (Not (k = Z)) -> (proofType Z k k)) ->
(proofExtend : {a1 : Nat} -> {b1 : Nat} -> {g1 : Nat} -> {r1 : Nat} -> {q1 : Nat} -> (proofType b1 r1 g1) -> (a1 = r1 + (q1 * b1)) -> (isGCD b1 r1 g1) -> (proofType a1 b1 g1)) ->
(g : Nat ** ((isGCD a b g), (proofType a b g)))

euclidGCDExtend a b notBothZ proofType baseLeft baseRight proofExtend =
	(euclidRecursion a b notBothZ (\a => (\b => (typeNew a b))) baseLeftNew baseRightNew extendNew) where

	typeNew : Nat -> Nat -> Type
	typeNew a b = (g : Nat ** ((isGCD a b g), (proofType a b g)))

	baseLeftNew : (k : Nat) -> (Not (k = Z)) -> (typeNew k Z)
	baseLeftNew k notZ = (k ** ((snd (gcdRightZero k notZ)), (baseLeft k notZ)))

	baseRightNew : (k : Nat) -> (Not (k = Z)) -> (typeNew Z k)
	baseRightNew k notZ = (k ** ((snd (gcdLeftZero k notZ)), (baseRight k notZ)))

	extendNew : {a1 : Nat} -> {b1 : Nat} -> {r1 : Nat} -> {q1 : Nat} -> (typeNew b1 r1) -> (a1 = r1 + (q1 * b1)) -> (typeNew a1 b1)
	extendNew (g ** (proofGCD, proofAux)) proofEq = (g ** ((remainderExtendsGCD proofGCD proofEq), (proofExtend proofAux proofEq proofGCD)))

----------------------------------------------------------------------------------------------

--More proofs

|||Proof that if g = gcd (a, b) and n != 0, n * g = gcd (n * a, n * b)
gcdMult : {a : Nat} -> {b : Nat} -> {g : Nat} ->
		(isGCD a b g) -> (n : Nat) -> (Not (n = Z)) -> (isGCD (n * a) (n * b) (n * g))

gcdMult {a} {b} {g} proofGCD n notZ = ((euclidRecursion a b (gcdImpliesNotBothZ proofGCD) (\a => (\b => proofType a b)) baseLeft baseRight proofExtend) g proofGCD n notZ) where

	proofType : Nat -> Nat -> Type
	proofType a1 b1 = (g1 : Nat) -> (isGCD a1 b1 g1) -> (n1 : Nat) -> (Not (n1 = Z)) -> (isGCD (n1 * a1) (n1 * b1) (n1 * g1))

	baseLeft : (k : Nat) -> (Not (k = Z)) -> (proofType k Z)
	baseLeft k kNotZ g1 prfGCD n1 nNotZ = (eqConservesGCD Refl (sym (multZeroRightZero n1)) proofEq (snd (gcdRightZero (n1 * k) (nonZeroMultNotZero nNotZ kNotZ)))) where
		proofEq = (cong {f = (\l => n1 * l)} (gcdRightZeroRefl k (g1 ** prfGCD)))

	baseRight : (k : Nat) -> (Not (k = Z)) -> (proofType Z k)
	baseRight k kNotZ g1 prfGCD n1 nNotZ = (eqConservesGCD (sym (multZeroRightZero n1)) Refl proofEq (snd (gcdLeftZero (n1 * k) (nonZeroMultNotZero nNotZ kNotZ)))) where
		proofEq = (cong {f = (\l => n1 * l)} (gcdLeftZeroRefl k (g1 ** prfGCD)))

	proofExtend : {a1 : Nat} -> {b1 : Nat} -> {r1 : Nat} -> {q1 : Nat} -> (proofType b1 r1) -> (a1 = r1 + (q1 * b1)) -> (proofType a1 b1)
	proofExtend {a1} {b1} {r1} {q1} remProof proofEq g1 prfGCD n1 nNotZ = (remainderExtendsGCD (remProof g1 (remainderConservesGCD prfGCD proofEq) n1 nNotZ) (extendEqualMult proofEq n1))



|||Proof that d divides (a * b) and d and a are coprime implies d divides b
coprimeImpliesDiv : {d : Nat} -> {a : Nat} -> {b : Nat} ->
				(isDivisible (a * b) d) -> (coprime a d) -> (isDivisible b d)
coprimeImpliesDiv {d} {a} {b = Z} (k ** (proofDiv, notZ)) _ = zeroDivisible notZ
coprimeImpliesDiv {d} {a} {b = (S n)} (k ** (proofDiv, notZ)) proofCoprime = eqConservesDivisible ((snd (gcdMult (coprimeImpliesGCDOne proofCoprime) (S n) SIsNotZ)) d (eqConservesDivisible (k ** (proofDiv, notZ)) (multCommutative a (S n)) Refl, dividesMultiple (divisionReflexive notZ) (S n))) (multOneRightNeutral (S n)) Refl

----------------------------------------------------------------------------------------------



--deprecated functions

{-

|||Returns gcd (a, b) with proof that it is the gcd (helper function with bound to make euclidGCD total)
euclidGCDBound : (bound : Nat) -> (a : Nat) -> (b : Nat) -> (LTE a bound) -> (LTE (S b) bound) -> (Either (Not (a = Z)) (Not (b = Z))) -> (d : Nat ** (isGCD a b d))

euclidGCDBound bound a b leftLTE rightLTE notBothZ =
	euclidGCDBoundGen bound a b leftLTE rightLTE notBothZ isGCD baseLeft baseRight remainderExtendsGCD where
		baseLeft = (\a => (\notZ => (a ** ((zeroCommonDivisorRight notZ, (\n => (\proofCommonDivisor => (fst proofCommonDivisor))))))))
		baseRight = (\b => (\notZ => (b ** (zeroCommonDivisorLeft notZ, (\n => (\proofCommonDivisor => (snd proofCommonDivisor)))))))



euclidGCDBound _ Z Z _ _ notBothZ =
	case notBothZ of
		Left notZ => void (notZ Refl)
		Right notZ => void (notZ Refl)
euclidGCDBound _ (S a) Z _ _ _ = ((S a) ** ((zeroCommonDivisorRight SIsNotZ, (\n => (\proofCommonDivisor => (fst proofCommonDivisor))))))
euclidGCDBound _ Z (S b) _ _ _ = ((S b) ** (zeroCommonDivisorLeft SIsNotZ, (\n => (\proofCommonDivisor => (snd proofCommonDivisor)))))
euclidGCDBound Z (S a) (S b) lteLeft lteRight _ = void (succNotLTEzero lteLeft)
euclidGCDBound (S bound) (S a) (S b) (LTESucc lteLeft) (LTESucc lteRight) notBothZ =
	case (euclidDivide (S a) (S b) SIsNotZ) of
	(q ** (r ** (proofEq, proofLNEQ))) =>
		case (euclidGCDBound bound (S b) r lteRight (lteTransitive (lneqToLT proofLNEQ) lteRight) (Left SIsNotZ)) of
		(d ** proofGCD) =>
			(d ** remainderExtendsGCD SIsNotZ proofEq proofGCD)
-}



{-

euclidGCD a b notBothZ =
	case (isLTE a b) of
		(Yes proofLTE) => euclidGCDBound (S b) a b (lteTransitive proofLTE (lteSuccRight lteRefl)) lteRefl notBothZ
		(No proofNotLTE) => euclidGCDBound (S a) a b (lteSuccRight lteRefl) (LTESucc (notLTEImpliesGTE proofNotLTE)) notBothZ

-}
