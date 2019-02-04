module Linear

import Rationals
import Data.Vect

data SolExists : Type where
  YesExists : SolExists
  DNExists : SolExists

--Solving a linear equation ax + b = 0
--zcase and ncase are proofs to be provided.
eqSolver : (a: Integer) -> (b : Integer) ->
  Either (x : Pair ** (SolExists, (fst x)*a + (snd x)*b = 0)) (SolExists)
eqSolver a b = if (isNotZero (toNat (abs a))) then Left (simplifyRational (-b, a) ** (YesExists, ?ncase))
  else check where
  check = if (isNotZero (toNat (abs b))) then Right DNExists else Left ((0,0) ** (YesExists, ?zcase))
