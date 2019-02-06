module Linear

import ZZ
import Rationals
import Data.Vect

data SolExists : Type where
  YesExists : SolExists
  DNExists : SolExists

ApZZ : (f: ZZ -> ZZ)-> n = m -> f n = f m
ApZZ f Refl = Refl

ZeroSum: (a: ZZ) -> (b: ZZ) -> (a = 0) -> (b = 0) -> (a + b = 0)
ZeroSum (fromInt(0)) (fromInt(0)) Refl Refl = Refl

triviality: (a: ZZ) -> (b: ZZ) -> (b = 0) -> (a*b=0)
triviality a b prf = trans (apZZ (\x => a*x) b 0 prf) (multZeroRightZeroZ(a))

triviality2: (a: ZZ) -> (0*a=0)
triviality2 a = multZeroLeftZeroZ(a)

ZeroProof: (a: ZZ) -> (b: ZZ) -> (b = 0) -> (0*a + 1*b = 0)
ZeroProof a b prf = trans (trans (ApZZ (\x=> x + 1*b) (triviality2 a)) (ApZZ (\x => 0 + x) (triviality 1 b prf))) (ZeroSum 0 0 Refl Refl)

--Solving a linear equation ax + b = 0 in the case when b = 0 (Basically, this shows that ax=0 is uniquely solved by (0,1))

trivialeqSolver : (a: ZZ) -> (b : ZZ) -> (b = 0) -> Either (x : ZZPair ** (SolExists, (fst x)*a + (snd x)*b = 0)) (SolExists)
trivialeqSolver a b prf = Left ((0,1) ** (YesExists, (ZeroProof a b prf)))

eqSolver : (a: ZZ) -> (b : ZZ) -> Either (x : ZZPair ** (SolExists, (fst x)*a + (snd x)*b = 0)) (SolExists)
eqSolver a b = Left (simplifyRational (-b, a) ** (YesExists, ?ncase))
