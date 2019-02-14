module Rationals

data NotZero : Integer -> Type where --Proof that a number is not zero, needed to construct Q
  OneNotZero : NotZero 1
  NegativeNotZero : ( n: Integer ) -> NotZero n -> NotZero (-n)
  PositiveNotZero : ( m: Integer ) -> LTE 1 (fromIntegerNat m)  -> NotZero m

rational : (p: Nat) -> (q: Integer) -> NotZero q -> (Integer, Integer)
rational Z q x = (toIntegerNat(0), q)
rational (S k) q x = (toIntegerNat(S k), q)

SecondPart : (Integer, Integer) -> Integer
SecondPart x = (snd x)

InclusionMap : (n : Nat) -> (Integer, Integer) --Includes the naturals in Q
InclusionMap n = rational n 1 OneNotZero

AddRationals : (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer) --Need to implement proof checking for nonzero denominators
AddRationals x y = ((fst x)*(snd y) + (snd x)*(fst y), (snd x)*(snd y))

MultiplyRationals : (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer) --Need to implement proof checking for nonzero denominators
MultiplyRationals  x y = ((fst x)*(fst y), (snd x)*(snd y))

--Need to create multiplicative inverses of rationals as well

--A GCD function with proof that it is the GCD would be useful to reduce rationals into simplified form

test : Nat
test = fct 3
