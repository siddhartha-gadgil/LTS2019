module Rationals

import ZZ
import ZZUtils
import GCDZZ
import Divisors
import BoundedGCD

%default total

-- Everything in this file is total. 

-- The functions below are completely based on the code from GCDZZ; they were written to improve
-- readability.

Quotient: (a: ZZ) -> (b: ZZ) -> (IsNonNegative a) -> (IsPositive b) -> (ZZ)
Quotient a b x y = Prelude.Pairs.DPair.fst (QuotRemZ a b x y)

Remainder: (a: ZZ) -> (b: ZZ) -> (IsNonNegative a) -> (IsPositive b) -> (ZZ)
Remainder a b x y = Prelude.Pairs.DPair.fst(Prelude.Pairs.DPair.snd (QuotRemZ a b x y))

%access public export

Pair : Type
Pair = (Integer, Integer)



ZZPair : Type
ZZPair = (ZZ, ZZ)

ZZtoDb : ZZ -> Double
ZZtoDb x = cast{from=Integer}{to=Double} (cast{from=ZZ}{to=Integer} x)

DbtoZZ : Double -> ZZ
DbtoZZ x = cast{from=Integer}{to=ZZ} (cast{from=Double}{to=Integer} x)

isNotZero :  Nat -> Bool
isNotZero Z = False
isNotZero (S k) = True

isFactorInt : Integer -> Integer -> Type  --Needed for defining Integer division
isFactorInt m n = (k : Integer ** (m * k = n))

divides : (m: Integer) -> (n: Integer) -> (k: Integer ** (m * k = n)) -> Integer
divides m n k = (fst k)

--Integer implemetation of gcd
CalcGCD : (Integer, Integer) -> Integer
CalcGCD (a, b) = case (decEq b 0) of
                      (Yes prf) => a
                      (No contra) => toIntegerNat (gcdAlgo (toNat a) (toNat b))

OnlyPositive : (x: Pair) -> Pair
OnlyPositive x = (if (fst x)>0 then fst x else (-1)*(fst x), if(snd x)>0 then (snd x) else (-1)*(snd x))

--Integer implemetation of gcd
gccd : (Integer, Integer) -> Integer
gccd x = CalcGCD (OnlyPositive x)

data ZZNotZero : ZZ -> Type where
  ZZOneNotZero : ZZNotZero 1
  ZZNegativeNotZero : ( n: ZZ ) -> ZZNotZero n -> ZZNotZero (-n)
  ZZPositiveNotZero : ( m: ZZ ) -> LTE 1 (fromIntegerNat (cast(m)))  -> ZZNotZero m

-- A section on the custom equality of Rationals

||| If a is not equal to zero and b is not equal to zero, their product is not equal to zero.
productNonZero: (NotZero a) -> (NotZero b) -> (NotZero (a*b))
productNonZero PositiveZ PositiveZ = PositiveZ
productNonZero PositiveZ NegativeZ = NegativeZ
productNonZero NegativeZ PositiveZ = NegativeZ
productNonZero NegativeZ NegativeZ = PositiveZ

|||A rational number is equal to its component representation (Numerator,Denominator)
pairIsComponents: (x: ZZPair) -> (x=((fst x), (snd x)))
pairIsComponents (a, b) = Refl

--Type for equality of two Rationals
EqRat : (x: ZZPair) -> (NotZero (snd x)) -> (y: ZZPair) -> (NotZero (snd y)) -> Type
EqRat x a y b = (fst x)*(snd y)=(snd x)*(fst y)

|||The analog of 'Refl' for equality of rationals.
EqRatRefl: (x: ZZPair) -> (a: NotZero (snd x)) -> (EqRat x a x a)
EqRatRefl x a = rewrite (multCommutativeZ (fst x) (snd x)) in
                  Refl

|||The analog of 'sym' for equality of rationals.
EqRatSym: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (EqRat x a y b) -> (EqRat y b x a)
EqRatSym x a y b z = rewrite (multCommutativeZ (snd y) (fst x)) in
                     rewrite (multCommutativeZ (fst y) (snd x)) in
                      sym z


equalMeansEqualPairs: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (x=y) -> (((fst x), (snd x)) = ((fst y), (snd y)))
equalMeansEqualPairs x a y b prf = rewrite sym (pairIsComponents x) in
                                   rewrite sym (pairIsComponents y) in
                                     prf


equalMeansCompEqual: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (x=y) -> ((fst x)=(fst y), (snd x)=(snd y))
equalMeansCompEqual y a y b Refl = (Refl, Refl)

eqMeansEqRat: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (x=y) -> (EqRat x a y b)
eqMeansEqRat y a y b Refl = rewrite (multCommutativeZ (fst y) (snd y)) in
                             Refl

|||(0,1) is "equal" to (0,k) for any nonzero k
reducedFormZeroLeft: {k: ZZ} -> (a: NotZero k) -> (EqRat (0,1) PositiveZ (0,k) a)
reducedFormZeroLeft {k} a = rewrite (multZeroLeftZeroZ (k)) in
                              Refl

|||(0,k) is "equal" to (0,1) for any nonzero k
reducedFormZeroRight: (k: ZZ) -> (a: NotZero k) -> (EqRat (0,k) a (0,1) PositiveZ )
reducedFormZeroRight k a = rewrite (multZeroRightZeroZ (k)) in
                              Refl

||| (1,1) is "equal" to (k,k) for any nonzero k
reducedFormOneLeft: {k: ZZ} -> (a: NotZero k) -> (EqRat (1,1) PositiveZ (k,k) a)
reducedFormOneLeft {k} a = Refl

||| (k,k) is "equal" to (1,1) for any nonzero k
reducedFormOneRight: (k: ZZ) -> (a: NotZero k) -> (EqRat (k,k) a (1,1) PositiveZ)
reducedFormOneRight k a = Refl
|||If a = b and c = d, a*c = b*d
multEqualEqual: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (d: ZZ) -> (a=b) -> (c=d) -> (a*c=b*d)
multEqualEqual b b d d Refl Refl = Refl

-- some helper functions for the first case of transitivity

transH1: {x: ZZPair} -> {y: ZZPair} -> {z: ZZPair} -> (((fst x)*(snd y)) = ((snd x)*(fst y))) -> (((fst y)*(snd z)) = ((snd y)*(fst z))) ->
((((fst x)*(snd y))*((fst y)*(snd z))) = (((snd x)*(fst y))*((snd y)*(fst z))))
transH1 {x} {y} {z} prf prf1 = (multEqualEqual ((fst x)*(snd y)) ((snd x)*(fst y)) ((fst y)*(snd z)) ((snd y)*(fst z)) prf prf1)

transH2: {x: ZZPair} -> {y: ZZPair} -> {z: ZZPair} -> ((((fst x)*(snd y))*((fst y)*(snd z))) = (((snd x)*(fst y))*((snd y)*(fst z))))
-> ((((fst x)*(snd z))*((fst y)*(snd y))) = (((snd x)*(fst z))*((fst y)*(snd y))))
transH2 {x} {y} {z} prf = rewrite (sym (multAssociativeZ (fst x) (snd z) ((fst y)*(snd y)) ) ) in
                          rewrite (sym (multAssociativeZ (snd x) (fst z) ((fst y)*(snd y)) ) ) in
                          rewrite (multCommutativeZ (fst y) (snd y)) in
                          rewrite (multAssociativeZ (snd z) (snd y) (fst y)) in
                          rewrite (multAssociativeZ (fst x) ((snd z)*(snd y)) (fst y) ) in
                          rewrite (multCommutativeZ (snd z) (snd y)) in
                          rewrite (multAssociativeZ (fst z) (snd y) (fst y)) in
                          rewrite (multCommutativeZ (fst z) (snd y)) in
                          rewrite (multAssociativeZ (fst x) (snd y) (snd z)) in
                          rewrite (multCommutativeZ ((snd y)*(fst z)) (fst y)) in
                          rewrite (multAssociativeZ (snd x) (fst y) ((snd y)*(fst z))) in
                          rewrite (sym (multAssociativeZ ((fst x)*(snd y)) (snd z) (fst y))) in
                          rewrite (multCommutativeZ (snd z) (fst y)) in
                          prf

transH3: {x: ZZPair} -> {y: ZZPair} -> {z: ZZPair} -> ((((fst x)*(snd z))*((fst y)*(snd y))) = (((snd x)*(fst z))*((fst y)*(snd y))))
-> (b: NotZero (snd y)) -> (k: NotZero (fst y)) -> (((fst x)*(snd z)) = ((snd x)*(fst z)))
transH3 {x} {y} {z} prf b k = (multRightCancelZ ((fst x)*(snd z)) ((snd x)*(fst z)) ((fst y)*(snd y)) (productNonZero k b) prf)

|||Nothing is both zero and nonzero.
NotZeroAndNonZero: (k: ZZ) -> (k=0) -> (NotZero k) -> Void
NotZeroAndNonZero (Pos (S _)) Refl PositiveZ impossible
NotZeroAndNonZero (NegS _) Refl NegativeZ impossible


|||The integers are an integral domain.
ZZIntegralDomain: (a: ZZ) -> (b: ZZ) -> (a*b=0) -> (NotZero b) -> (a=0)
ZZIntegralDomain a b prod bNZ = case (decZero a) of
                                    (Yes aNZ) => void (NotZeroAndNonZero (a*b) prod (productNonZero aNZ bNZ))
                                    (No contra) => notNotZeroThenZero (contra)


flipSidesAndTerms: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (d: ZZ) -> (a*b=c*d) -> (d*c=b*a)
flipSidesAndTerms a b c d prf = rewrite (multCommutativeZ (b) (a)) in
                                rewrite (multCommutativeZ (d) (c)) in
                                  sym prf


|||If ab=cd and d =0 but b is not zero, then a is zero.
zeroProductZero1: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (d: ZZ) -> (a*b=c*d) -> (d = 0) -> (NotZero b) -> (a=0)
zeroProductZero1 a b c d prod dZ bNZ = ZZIntegralDomain (a) (b) (trans (prod) (trans (multEqualEqual c c d (Pos 0) Refl dZ) (multZeroRightZeroZ (c)) )) (bNZ)

|||If ab=cd and a=0 but c is not zero, then d is zero.
zeroProductZero2: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (d: ZZ) -> (a*b=c*d) -> (a = 0) -> (NotZero c) -> (d=0)
zeroProductZero2 a b c d prod aZ cNZ = zeroProductZero1 d c b a (flipSidesAndTerms a b c d prod) aZ cNZ

|||If the numerator is zero, the fraction is zero.
allZeroesSame: (x: ZZPair) -> (a: NotZero (snd x)) -> (z: ZZPair) -> (c: NotZero (snd z)) -> (fst x = 0) -> (fst z = 0)
-> EqRat x a z c
allZeroesSame x a z c prf prf1 = rewrite prf in
                                 rewrite prf1 in
                                 rewrite multZeroLeftZeroZ (snd z) in
                                 rewrite multZeroRightZeroZ (snd x) in
                                  Refl

|||The analog of 'trans' for rationals.
EqRatTrans: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) ->
(z: ZZPair) -> (c: NotZero (snd z)) -> (EqRat x a y b) -> (EqRat y b z c) -> (EqRat x a z c)
EqRatTrans x a y b z c pxy pyz = case (decZero (fst y)) of
                                      (Yes k) => (transH3 {x} {y} {z} (transH2 {x} {y} {z} (transH1 {x} {y} {z} pxy pyz)) b k )
                                      (No contra) => (allZeroesSame x a z c (zeroProductZero1 (fst x) (snd y) (snd x) (fst y) pxy (notNotZeroThenZero (contra)) b ) (zeroProductZero2 (fst y) (snd z) (snd y) (fst z) pyz (notNotZeroThenZero (contra)) b ))

-- NOTE: there is another case to be filled in. In the first case, cancellation is possible if the
-- numerator is nonzero. However, if the numerator of Y is zero, then it remains to be shown that
-- X and Z are (0,(snd x)) and (0,(snd z)) respectively (and are thus 'equal').

make_rational : (p: Nat) -> (q: ZZ) -> ZZNotZero q -> ZZPair
make_rational p q x = (fromInt(toIntegerNat(p)), q)

InclusionMap : (n : Nat) -> ZZPair --Includes the naturals in Q
InclusionMap n = make_rational n 1 ZZOneNotZero

AddRationals : (x: ZZPair) -> NotZero (snd x) -> (y: ZZPair) -> NotZero (snd y) -> ZZPair
AddRationals x a y b = ((fst x)*(snd y) + (snd x)*(fst y), (snd x)*(snd y))

MultiplyRationals : (x: ZZPair) -> NotZero (snd x) -> (y: ZZPair) -> NotZero (snd y) -> ZZPair
MultiplyRationals x a y b =((fst x)*(fst y), (snd x)*(snd y))

MultInverse : (x: ZZPair) -> NotZero (fst x) -> NotZero (snd x) -> ZZPair
MultInverse x y z = ((snd x), (fst x))

AddInverse : (x: ZZPair) -> NotZero (snd x) -> ZZPair
AddInverse x a = (-(fst x), (snd x))

Subtraction : (x: ZZPair) -> NotZero (snd x) -> (y: ZZPair) -> NotZero (snd y) -> ZZPair
Subtraction x a y b = AddRationals x a (AddInverse y b) b

Division : (x: ZZPair) -> NotZero (snd x) -> (y: ZZPair) -> NotZero (fst y) -> NotZero (snd y) -> ZZPair
Division x a y b c = MultiplyRationals x a (MultInverse y b c) b

Scaling: (a: ZZ) -> (x: ZZPair) -> ZZPair
Scaling a x = (a*(fst x), (snd x))

remZeroDivisible: (a: ZZ) -> (b: ZZ) -> (quot: ZZ) -> (rem: ZZ) -> (a = rem + quot*b) -> (rem = 0) -> (a=quot*b)
remZeroDivisible a b quot rem prf prf1 = rewrite sym (plusZeroLeftNeutralZ (quot*b)) in
                                         rewrite sym prf1 in
                                         prf

IsRationalZPOS: (x: ZZPair) -> (prf1 :IsNonNegative (fst x)) -> (prf2: IsPositive (snd x)) -> Either (quot: ZZ ** ((fst x)=quot*(snd x))) (NotZero (fst (snd (QuotRemZ (fst x) (snd x) prf1 prf2) )) )
IsRationalZPOS x prf1 prf2 = case (decEq (fst (snd (QuotRemZ (fst x) (snd x) prf1 prf2))) (Pos Z)) of
                          (Yes prf) => Left ( (Quotient (fst x) (snd x) prf1 prf2) **
                          (remZeroDivisible (fst x) (snd x) (Quotient (fst x) (snd x) prf1 prf2) (Remainder (fst x) (snd x) prf1 prf2) (Prelude.Basics.fst (Prelude.Pairs.DPair.snd (Prelude.Pairs.DPair.snd (QuotRemZ (fst x) (snd x) prf1 prf2)) )) prf ) )
                          (No contra) => Right (nonZeroNotZero (fst (snd (QuotRemZ (fst x) (snd x) prf1 prf2))) contra)


CheckIsQuotientZ: (a: ZZ) -> (b: ZZ) -> (NotZero b) -> Either (quot: ZZ ** (a=quot*b)) (ZZPair)
CheckIsQuotientZ a (Pos Z) x impossible
CheckIsQuotientZ (Pos Z) (Pos (S j)) x = case ((IsRationalZPOS ((Pos Z), (Pos (S j))) NonNegative Positive)) of
                                            (Left l) => (Left l)
                                            (Right r) => Right ((Pos Z),(Pos (S j)))
CheckIsQuotientZ (Pos (S k)) (Pos (S j)) x = case ((IsRationalZPOS ((Pos (S k)), (Pos (S j))) NonNegative Positive)) of
                                            (Left l) => (Left l)
                                            (Right r) => Right ((Pos (S k)), (Pos (S j)))
CheckIsQuotientZ (NegS k) (Pos (S j)) x = case ((IsRationalZPOS ((Pos (S k)), (Pos (S j))) NonNegative Positive)) of
                                            (Left l) =>  Left (QRproof1 (Pos (S k)) (Pos (S j)) Refl Refl l)
                                            (Right r) => Right ((Pos (S k)), (Pos (S j)))
CheckIsQuotientZ (Pos Z) (NegS j) x = Left (Pos Z ** Refl)
CheckIsQuotientZ (Pos (S k)) (NegS j) x = case ((IsRationalZPOS ((Pos (S k)), (Pos (S j))) NonNegative Positive)) of
                                            (Left l) =>  Left (QRproof3 (Pos (S k)) (Pos (S j)) Refl Refl l)
                                            (Right r) => Right ((Pos (S k)), (Pos (S j)))
CheckIsQuotientZ (NegS k) (NegS j) x = case ((IsRationalZPOS ((Pos (S k)), (Pos (S j))) NonNegative Positive)) of
                                            (Left l) =>  Left (QRproof4 (Pos (S k)) (Pos (S j)) Refl Refl l)
                                            (Right r) => Right ((Pos (S k)), (Pos (S j)))

-- The following section is on simplification of rationals. There was a function written earlier,
-- called simplifyRational which used the existence of the numeric type 'Double' in Idris so that
-- simplification could actually be done. This has now been superseded by the functions below as
-- the GCD with proof has now been implemented.

-- aByd and bByd are taken from the file 'Divisors.idr' (by Shafil)

|||Extracts a/gcd(a,b) from the definition of GCDZ
aBydNum:GCDZ a b d ->ZZ
aBydNum dGcdab = (fst (fst (fst (snd dGcdab))))

|||Extracts b/gcd(a,b) from the definition of GCDZ
bBydDen:GCDZ a b d ->ZZ
bBydDen dGcdab = (fst (snd (fst (snd dGcdab))))

|||A helper routine which simplifies a rational number.
simplification: (a: ZZ) -> (b: ZZ) -> (NotBothZeroZ a b) -> (y: ZZPair ** (GCDZ (fst y) (snd y) 1))
simplification a b prf = ((aBydNum (snd (gcdZZ a b prf)), bBydDen (snd (gcdZZ a b prf))) ** (divideByGcdThenGcdOne (snd (gcdZZ a b prf))))

|||If b is not zero, then it is not the case that both 'a' and 'b' are zero.
NotZeroNotBothZero: (a: ZZ) -> (b: ZZ) -> (NotZero b) -> (NotBothZeroZ a b)
NotZeroNotBothZero a (Pos (S k)) PositiveZ = RightPositive
NotZeroNotBothZero a (NegS k) NegativeZ = RightNegative

|||This takes a rational number and simplifies it and provides a proof that it is simplified
|||(that is, the numerator and denominator have GCD 1)
simplifyWithProof: (x: ZZPair) -> (NotZero (snd x)) -> (y: ZZPair ** (GCDZ (fst y) (snd y) 1))
simplifyWithProof x prf = (simplification (fst x) (snd x) (NotZeroNotBothZero (fst x) (snd x) prf))

|||Extracting the simplified rational from the dependent pair.
simplifyRationalProof: (x: ZZPair) -> (NotZero (snd x)) -> ZZPair
simplifyRationalProof x prf = fst (simplifyWithProof x prf)

-- below is the old function simplifyRational. I need to make the GCD-based code above
-- compatible with the code that implements simplifyRational before replacing it.

--To prove that the SimplifyRational works, we can just check if the output is equal to the input
-- To be done
simplifyRational : (x : ZZPair) -> ZZPair
simplifyRational (a, b) = (sa, sb) where
  sa = DbtoZZ (da / g) where
    da = ZZtoDb a
    g = cast {from=Integer} {to=Double}
      (gccd (cast {from=ZZ} {to=Integer}a,cast {from=ZZ} {to=Integer}b))
  sb = DbtoZZ (db / g) where
    db = ZZtoDb b
    g = cast {from=Integer} {to=Double}
      (gccd (cast {from=ZZ} {to=Integer}a,cast {from=ZZ} {to=Integer}b))

--Above, I will need to supply a proof that the GCD divides the two numbers. Then, the function defined above will produce the rational in simplified form.

xAndInverseNotZeroPlus : (x: ZZPair) -> (k: NotZero (snd x)) -> (NotZero (snd (AddInverse x k)))
xAndInverseNotZeroPlus x k = k

xAndInverseNotZeroMult : (x: ZZPair) -> (j: NotZero (fst x)) -> (k: NotZero (snd x)) -> (NotZero (snd (MultInverse x j k)))
xAndInverseNotZeroMult x j k = j





{-
FirstIsInverted : (x: ZZPair) -> (k: ZZNotZero (snd x)) -> (a: ZZ) -> (a = (fst x)) -> ((-a) = fst (AddInverse x k))
FirstIsInverted x k a prf = (apZZ (\x => -x) a (fst x) prf)

SecondStaysSame : (x: ZZPair) -> (k: ZZNotZero (snd x)) -> (b: ZZ) -> (b = (snd x)) -> (b = (snd (AddInverse x k)))
SecondStaysSame x k b prf = (apZZ (\x => x) b (snd x) prf)

xplusinverse: (x: ZZPair) -> (k: ZZNotZero (snd x)) -> ZZPair
xplusinverse x k = AddRationals x k (AddInverse x k) (xAndInverseNotZero x k)

addinverselemma: (a: ZZ) -> (b: ZZ) -> ((-a)=b) -> (a + b = ((-a) + a)) -> ((-a)+a =0 ) -> (a + b = 0)
addinverselemma a b prf prf1 prf2 = trans prf1 prf2

addinverseFST: (x: ZZPair) -> (k: ZZNotZero (snd x)) -> (a: ZZ) -> (a = (fst x)) -> (fst (AddInverse x k) = b) -> ((-a) = b)
addinverseFST x k a prf prf1 = trans (FirstIsInverted x k a prf) (prf1)

addinverseSND: (x: ZZPair) -> (k: ZZNotZero (snd x)) -> (c: ZZ) -> (c = (snd x)) -> (snd (AddInverse x k) = b) -> (c = b)
addinverseSND x k c prf prf1 = trans (SecondStaysSame x k c prf) (prf1)
-}

-- Proving the field axioms to show that Q is a field.
-- The first section concerns those axioms which involve only one or two elements of Q.


|||AddRationals is commutative
plusCommutativeQ: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (AddRationals x a y b) = (AddRationals y b x a)
plusCommutativeQ x a y b = rewrite (multCommutativeZ (snd y) (snd x)) in
                           rewrite (plusCommutativeZ ((fst x)*(snd y)) ((snd x)*(fst y))) in
                           rewrite (multCommutativeZ (snd x) (fst y)) in
                           rewrite (multCommutativeZ (snd y) (fst x)) in
                           Refl

|||MultiplyRationals is commutative
multCommutativeQ: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (MultiplyRationals x a y b) = (MultiplyRationals y b x a)
multCommutativeQ x a y b = rewrite (multCommutativeZ (fst x) (fst y)) in
                           rewrite (multCommutativeZ (snd x) (snd y)) in
                           Refl

||| Zero is the right additive identity, meaning that x + 0 = x
zeroAddIdentityRight: (x: ZZPair) -> (a: NotZero (snd x)) -> ((AddRationals x a (0,1) PositiveZ) = x)
zeroAddIdentityRight x a = rewrite (multZeroRightZeroZ (snd x)) in
                      rewrite (multOneRightNeutralZ (fst x)) in
                      rewrite (plusZeroRightNeutralZ (fst x)) in
                      rewrite (multOneRightNeutralZ (snd x)) in
                      rewrite (sym (pairIsComponents x)) in
                      Refl

||| Zero is the left additive identity, meaning that 0 + x = x
zeroAddIdentityLeft: (x: ZZPair) -> (a: NotZero (snd x)) -> ((AddRationals (0,1) PositiveZ x a) = x)
zeroAddIdentityLeft x a = rewrite (multZeroLeftZeroZ (snd x)) in
                      rewrite (multOneLeftNeutralZ (fst x)) in
                      rewrite (plusZeroLeftNeutralZ (fst x)) in
                      rewrite (multOneLeftNeutralZ (snd x)) in
                      rewrite ((pairIsComponents x)) in
                      Refl

|||One is the right multiplicative identity (x*1=x)
oneMultIdentityRight: (x: ZZPair) -> (a: NotZero (snd x)) -> ((MultiplyRationals x a (1,1) PositiveZ) = x)
oneMultIdentityRight x a = rewrite (multOneRightNeutralZ (fst x)) in
                           rewrite (multOneRightNeutralZ (snd x)) in
                           rewrite (sym (pairIsComponents x)) in
                           Refl

|||One is the left multiplicative identity (1*x=x)
oneMultIdentityLeft: (x: ZZPair) -> (a: NotZero (snd x)) -> ((MultiplyRationals (1,1) PositiveZ  x a) = x)
oneMultIdentityLeft x a = rewrite (multOneLeftNeutralZ (fst x)) in
                           rewrite (multOneLeftNeutralZ (snd x)) in
                           rewrite ((pairIsComponents x)) in
                           Refl

||| x plus its additive inverse is equal to (0,(snd x)*(snd x)). A custom equality type is probably required to set
||| this equal to (0,1).
addInverseLeft: (x: ZZPair) -> (a: NotZero (snd x)) -> ((AddRationals x a (AddInverse x a) (xAndInverseNotZeroPlus x a)) = ((Pos 0), (snd x)*(snd x)))
addInverseLeft x a = rewrite (multCommutativeZ (fst x) (snd x)) in
                     rewrite (multNegateRightZ (snd x) (fst x)) in
                     rewrite (plusNegateInverseLZ ((snd x)*(fst x)) ) in
                     Refl

||| The additive inverse of x plus itself is equal to (0,(snd x)*(snd x)). A custom equality type is probably required to set
||| this equal to (0,1).
addInverseRight: (x: ZZPair) -> (a: NotZero (snd x)) -> ((AddRationals (AddInverse x a) (xAndInverseNotZeroPlus x a) x a) = (0, (snd x)*(snd x)))
addInverseRight x a = rewrite (multCommutativeZ (snd x) (fst x)) in
                      rewrite (multNegateLeftZ (fst x) (snd x)) in
                      rewrite (plusNegateInverseRZ ((fst x)*(snd x)) ) in
                      Refl

|||x times its multiplicative inverse is equal to ((fst x)*(snd x), (fst x)*(snd x)). A custom equality type is probably required to set
||| this equal to (1,1).
multInverseLeft: (x: ZZPair) -> (a: NotZero (fst x)) -> (b: NotZero (snd x)) ->
(MultiplyRationals x b (MultInverse x a b) (xAndInverseNotZeroMult x a b)) = ((fst x)*(snd x), (fst x)*(snd x))
multInverseLeft x a b = rewrite (multCommutativeZ (snd x) (fst x)) in
                        Refl

|||The multiplicative inverse of x times itself is equal to ((fst x)*(snd x), (fst x)*(snd x)). A custom equality type is probably required to set
||| this equal to (1,1).
multInverseRight: (x: ZZPair) -> (a: NotZero (fst x)) -> (b: NotZero (snd x)) ->
(MultiplyRationals (MultInverse x a b) (xAndInverseNotZeroMult x a b) x b ) = ((snd x)*(fst x), (snd x)*(fst x))
multInverseRight x a b = rewrite (multCommutativeZ (snd x) (fst x)) in
                         Refl


|||AddRationals is associative. It requires the helper function productNonZero.
plusAssociativeQ: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (z: ZZPair) -> (c: NotZero (snd z)) ->
((AddRationals (AddRationals x a y b) (productNonZero a b) z c) = (AddRationals x a (AddRationals y b z c) (productNonZero b c)))
plusAssociativeQ x a y b z c = rewrite (multAssociativeZ (snd x) (snd y) (snd z)) in
                               rewrite (multDistributesOverPlusLeftZ ((fst x)*(snd y)) ((snd x)*(fst y)) (snd z)) in
                               rewrite (sym (plusAssociativeZ (((fst x)*(snd y))*(snd z)) (((snd x)*(fst y))*(snd z)) (((snd x)*(snd y))*(fst z)) )) in
                               rewrite (sym (multAssociativeZ (snd x) (snd y) (fst z))) in
                               rewrite (sym (multAssociativeZ (snd x) (fst y) (snd z))) in
                               rewrite (sym (multAssociativeZ (fst x) (snd y) (snd z))) in
                               rewrite (multDistributesOverPlusRightZ (snd x) ((fst y)*(snd z)) ((snd y)*(fst z)) ) in
                               Refl


|||MultiplyRationals is associative. It requires the helper function productNonZero.
multAssociativeQ: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (z: ZZPair) -> (c: NotZero (snd z)) ->
((MultiplyRationals (MultiplyRationals x a y b) (productNonZero a b) z c) = (MultiplyRationals x a (MultiplyRationals y b z c) (productNonZero b c)))
multAssociativeQ x a y b z c = rewrite sym (multAssociativeZ (fst x) (fst y) (fst z)) in
                               rewrite sym (multAssociativeZ (snd x) (snd y) (snd z)) in
                               Refl



