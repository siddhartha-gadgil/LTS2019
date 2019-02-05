module Linear

import Data.ZZ
import Rationals
import Data.Vect

data SolExists : Type where
  YesExists : SolExists
  DNExists : SolExists

ZeroSum: (a: Nat) -> (b: Nat) -> (a = 0) -> (b = 0) -> (a + b = 0)
ZeroSum Z Z Refl Refl = Refl

triviality: (a: Nat) -> (b = 0) -> (a*b=0)
triviality a prf = trans (cong {f = \x => a*x} (prf)) (multZeroRightZero(a))

triviality2: (a: Nat) -> (0*a=0)
triviality2 a = Refl

ZeroProof: (a: Nat) -> (b: Nat) -> (b = 0) -> (0*a + 1*b = 0)
ZeroProof Z Z Refl = Refl
ZeroProof (S k) Z Refl = Refl

--Solving a linear equation ax + b = 0
--zcase and ncase are proofs to be provided.
eqSolver : (a: Integer) -> (b : Integer) ->
  Either (x : Pair ** (SolExists, (fst x)*a + (snd x)*b = 0)) (SolExists)
eqSolver a b = if (isNotZero (toNat (abs a))) then Left (simplifyRational (-b, a) ** (YesExists, ?ncase))
  else check where
  check = if (isNotZero (toNat (abs b))) then Right DNExists else Left ((0,0) ** (YesExists, ?zcase))
