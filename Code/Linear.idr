module Linear

import ZZ
import Rationals
import Data.Vect

data SolExists : Type where
  YesExists : SolExists
  DNExist : SolExists

isFactor : Nat -> Nat -> Type
isFactor m n = (k : Nat ** (m * k = n)) -- will be useful in solving Diophantine equations:
                                        -- if the denominator is a factor of the numerator, there is an integer solution

is_a_zero: (a: ZZ) -> Bool
is_a_zero (Pos Z) = True
is_a_zero (Pos (S k)) = False
is_a_zero (NegS k) = False

ApZZ : (f: ZZ -> ZZ)-> n = m -> f n = f m -- like apNat, but for ZZ
ApZZ f Refl = Refl

-- Helper functions for the case ax = 0 --

ZeroSum: (a: ZZ) -> (b: ZZ) -> (a = 0) -> (b = 0) -> (a + b = 0) --sum of two zeroes is zero
ZeroSum (fromInt(0)) (fromInt(0)) Refl Refl = Refl

triviality1: (a: ZZ) -> (b: ZZ) -> (b = 0) -> (a*b=0) -- premultiplying 0 by anything returns 0
triviality1 a b prf = trans (apZZ (\x => a*x) b 0 prf) (multZeroRightZeroZ(a))

triviality2: (a: ZZ) -> (0*a=0) -- 0 times anything is zero
triviality2 a = multZeroLeftZeroZ(a)

triviality3: (a: ZZ) -> (a*0=0) -- 0 times anything is zero
triviality3 a = multZeroRightZeroZ(a)

ZeroProof: (a: ZZ) -> (b: ZZ) -> (b = 0) -> (0*a + 1*b = 0) -- shows that the rational number (0,1) satisfies ax = 0
ZeroProof a b prf = trans (trans (ApZZ (\x=> x + 1*b) (triviality2 a)) (ApZZ (\x => 0 + x) (triviality1 1 b prf))) (ZeroSum 0 0 Refl Refl)

-- Helper functions for the case ax + b = 0

triviality4: (a: ZZ) -> (b: ZZ) -> (a*b = b*a)
triviality4 a b = multCommutativeZ a (b)

triviality5: (a: ZZ) -> (b: ZZ) -> (a*(-b)+b*a = a*(-b) + a*b )
triviality5 a b = ApZZ (\x=> a*(-b) + x) (triviality4 b a)

triviality6: (a: ZZ) -> (b: ZZ) -> ( (a*(-b)) + (a*b) = a*( (-b)+b ) )
triviality6 a b = sym ( multDistributesOverPlusRightZ a (-b) b )

triviality7: (a: ZZ) -> (b: ZZ) -> ( a*((-b) + b) = 0)
triviality7 a b = trans (ApZZ (\x => a*x) (plusNegateInverseRZ(b))) (triviality3(a))

SolutionProof: (a: ZZ) -> (b: ZZ) -> (a*(-b)+b*a=0)
SolutionProof a b = trans (trans (triviality5 a b) (triviality6 a b)) (triviality7 a b)

--Solving a linear equation ax + b = 0 in the case when b = 0 (Basically, this shows that ax=0 is uniquely solved by (0,1))

trivialeqSolver : (a: ZZ) -> (b : ZZ) -> (b = 0) -> Either (x : ZZPair ** (SolExists, (fst x)*a + (snd x)*b = 0)) (SolExists)
trivialeqSolver a b prf = Left ((0,1) ** (YesExists, (ZeroProof a b prf)))

-- Solving the linear equation ax+b = 0 in general

eqSolver : (a: ZZ) -> (b : ZZ) -> (ZZNotZero b) -> Either (x : ZZPair ** (SolExists, a*(fst x) + b*(snd x) = 0)) (SolExists)
eqSolver a b prf = case (is_a_zero(a)) of
  (True) => Right (DNExist)
  (False) => Left ((-b, a) ** (YesExists, (SolutionProof a b))) -- The solution is (-b/a), a rational number, with proof.

-- Helper functions for ax + b = c

helper1: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (a*(c+(-b))= a*c + a*(-b))
helper1 a b c = multDistributesOverPlusRightZ (a) (c) (-b)

helper2: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> ( a*(c-b) + b*a = a*c+ a*(-b)+ b*a )
helper2 a b c = ApZZ (\x => x+ b*a) (helper1 (a) (b) (c))

helper3: (a: ZZ) -> (b: ZZ) -> (a*(-b)+b*a=0)
helper3 a b = trans (trans (triviality5 a b) (triviality6 a b)) (triviality7 a b)

helper4: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (a*c + a*(-b) + b*a = a*c)
helper4 a b c = ?hole -- There is some issue here with Idris ; no matter what, it doesn't seem to accept this equality,
                      -- giving odd errors. This may be due to the fact that three numbers are being added, instead of two,
                      -- as done previously.


GeneralProof: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> ( a*(c-b) + b*a = a*c )
GeneralProof a b c = trans (helper2 a b c) (helper4 a b c)

-- Solving the linear equation ax + b = c (2x +3 = 7, for example) over the rationals

GeneralEqSolver: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (a0: ZZNotZero a) -> (b0: ZZNotZero b) -> (c0: ZZNotZero c) ->
(x : ZZPair ** (SolExists, a*(fst x) + b*(snd x) = (snd x)*c))
GeneralEqSolver a b c a0 b0 c0 = ( ( (c-b) , a ) ** (YesExists, (GeneralProof a b c) )) -- Solves the equation with proof

-- Now, we can use the rational solution of the linear equation ax + b = c to check whether this equation has an integer
-- solution; if it did, the denominator of the rational solution would divide the numerator. If it didn't, the equation
-- would have no solutions in the integers.