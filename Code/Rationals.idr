module Rationals

data NotZero : Integer -> Type where --Proof that a number is not zero, needed to construct Q
  OneNotZero : NotZero 1
  NegativeNotZero : ( n: Integer ) -> NotZero n -> NotZero (-n)
  PositiveNotZero : ( m: Integer ) -> LTE 1 (fromIntegerNat m)  -> NotZero m

isNotZero : Nat -> Bool
isNotZero Z = False
isNotZero (S k) = True

rational : (p: Nat) -> (q: Integer) -> NotZero q -> (Integer, Integer)
rational Z q x = (toIntegerNat(0), q)
rational (S k) q x = (toIntegerNat(S k), q)

{-
-- snd x can be used instead
SecondPart : (Integer, Integer) -> Integer
SecondPart x = (snd x)
-}

--To simplify rationals to coprime factors, Euclid's algo
gccd : (Integer, Integer) -> Integer
gccd (a, b) = if (isNotZero (toNat b)) then next else a where
  next = gccd (b, toIntegerNat (modNat (toNat a) (toNat b)))

--Lots of casts required to divide by GCD
simplifyRational : (Integer, Integer) -> (Integer, Integer)
simplifyRational (a, b) = (sa, sb) where
  sa = cast {from=Double} {to=Integer} (da / g) where
    da = cast {from=Integer} {to=Double} a
    g = cast {from=Integer} {to=Double} (gccd (a,b))
  sb = cast {from=Double} {to=Integer} (db / g) where
    db = cast {from=Integer} {to=Double} b
    g = cast {from=Integer} {to=Double} (gccd (a,b))

InclusionMap : (n : Nat) -> (Integer, Integer) --Includes the naturals in Q
InclusionMap n = rational n 1 OneNotZero

AddRationals : (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer) --Need to implement proof checking for nonzero denominators
AddRationals x y = simplifyRational ((fst x)*(snd y) + (snd x)*(fst y), (snd x)*(snd y))

MultiplyRationals : (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer) --Need to implement proof checking for nonzero denominators
MultiplyRationals  x y = simplifyRational ((fst x)*(fst y), (snd x)*(snd y))

--Equality of two rationals, needs to be made as a type instead of a bool
eqRat : (Integer, Integer) -> (Integer, Integer) -> Bool
eqRat x y = if ((fst x)*(snd y) == (snd x)*(fst y)) then True else False

--Inverse of a rational (requires proof that denom != 0)
inverseRat : (Integer, Integer) -> (Integer, Integer)
inverseRat x = simplifyRational ((snd x), (fst x))

--To do : Inverses are unique, except for equality (if b1 and b2 are inverses of a, b1 = b2)
--A GCD function with proof that it is the GCD would be useful to reduce rationals into simplified form
