module Rationals

import Data.ZZ

apInt : (f: Integer -> Integer) -> (n: Integer) -> (m: Integer) -> n = m -> f n = f m
apInt f m m Refl = Refl

isNotZero : Nat -> Bool
isNotZero Z = False
isNotZero (S k) = True

isFactorInt : Integer -> Integer -> Type  --Needed for defining Integer division
isFactorInt m n = (k : Integer ** (m * k = n))

divides : (m: Integer) -> (n: Integer) -> (k: Integer ** (m * k = n)) -> Integer
divides m n k = (fst k)

Pair : Type
Pair = (Integer, Integer)

Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat) --Euclidean algorithm implemented by Chinmaya
Eucl Z b = (0,0)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False => (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True => (0, S k)

--Integer implemetation of gcd
CalcGCD : (Integer, Integer) -> Integer
CalcGCD (a, b) = if (isNotZero (toNat b)) then next else a where
    next = CalcGCD (b, toIntegerNat (modNat (toNat a) (toNat b)))

OnlyPositive : (x: Pair) -> Pair
OnlyPositive x = (if (fst x)>0 then fst x else (-1)*(fst x), if(snd x)>0 then (snd x) else (-1)*(snd x))

--Integer implemetation of gcd
gccd : (Integer, Integer) -> Integer
gccd x = CalcGCD (OnlyPositive x)



data NotZero : Integer -> Type where --Proof that a number is not zero, needed to construct Q
  OneNotZero : NotZero 1
  NegativeNotZero : ( n: Integer ) -> NotZero n -> NotZero (-n)
  PositiveNotZero : ( m: Integer ) -> LTE 1 (fromIntegerNat m)  -> NotZero m

data ZZNotZero : ZZ -> Type where
  ZZOneNotZero : ZZNotZero 1
  ZZNegativeNotZero : ( n: ZZ ) -> ZZNotZero n -> ZZNotZero (-n)
  ZZPositiveNotZero : ( m: ZZ ) -> LTE 1 (fromIntegerNat (cast(m)))  -> ZZNotZero m


--Type for equality of two Rationals
data EqRat : Pair -> Pair -> Type where
  IdEq : (m : Pair) -> EqRat m m
  MulEq : (c : Integer) -> EqRat n m -> EqRat ((fst n)*c,(snd n)*c) m

make_rational : (p: Nat) -> (q: Integer) -> NotZero q -> Pair
make_rational p q x = (toIntegerNat(p), q)

InclusionMap : (n : Nat) -> Pair --Includes the naturals in Q
InclusionMap n = make_rational n 1 OneNotZero

AddRationals : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (snd y) -> Pair
AddRationals x a y b = ((fst x)*(snd y) + (snd x)*(fst y), (snd x)*(snd y))

MultiplyRationals : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (snd y) -> Pair
MultiplyRationals x a y b =((fst x)*(fst y), (snd x)*(snd y))

--Need proof that MultInverse x * x = 1
MultInverse : (x: Pair) -> NotZero (fst x) -> NotZero (snd x) -> Pair
MultInverse x y z = ((snd x), (fst x))

AddInverse : (x: Pair) -> NotZero (snd x) -> Pair
AddInverse x a = (-(fst x), (snd x))

Subtraction : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (snd y) -> Pair
Subtraction x a y b = AddRationals x a (AddInverse y b) b

Division : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (fst y) -> NotZero (snd y) -> Pair
Division x a y b c = MultiplyRationals x a (MultInverse y b c) b

--SimplifyRational : (x: Pair) -> NotZero (snd x) -> Pair
--SimplifyRational x a = (divides (gcdab fromIntegerNat((fst x)) fromIntegerNat((snd x))) ___ (fst x), divides (gcdab fromIntegerNat((fst x)) fromIntegerNat((snd x)) __ (snd x))

--To prove that the SimplifyRational works, we can just check if the output is equal to the input
-- To be done
simplifyRational : (x : Pair) -> Pair
simplifyRational (a, b) = (sa, sb) where
  sa = cast {from=Double} {to=Integer} (da / g) where
    da = cast {from=Integer} {to=Double} a
    g = cast {from=Integer} {to=Double} (gccd (a,b))
  sb = cast {from=Double} {to=Integer} (db / g) where
    db = cast {from=Integer} {to=Double} b
    g = cast {from=Integer} {to=Double} (gccd (a,b))

--Above, I will need to supply a proof that the GCD divides the two numbers. Then, the function defined above will produce the rational in simplified form.

ZZPair : Type
ZZPair = (ZZ, ZZ)

makeZZPair : Pair -> ZZPair
makeZZPair x = (fromInt(fst x), fromInt(snd x))

makePairZZ : ZZPair -> Pair
makePairZZ y = (cast(fst y), cast(fst y))

xAndInverseNotZero : (x: Pair) -> (k: NotZero (snd x)) -> NotZero (snd (AddInverse x k))
xAndInverseNotZero x (PositiveNotZero (snd x) y) = (PositiveNotZero (snd x) y)

FirstIsInverted : (x: Pair) -> (k: NotZero (snd x)) -> (a: Integer) -> (a = (fst x)) -> (-a = fst (AddInverse x k))
FirstIsInverted x k a prf = (apInt (\x => -x) a (fst x) prf)

SecondStaysSame : (x: Pair) -> (k: NotZero (snd x)) -> (b: Integer) -> (b = (snd x)) -> (b = (snd (AddInverse x k)))
SecondStaysSame x k b prf = (apInt (\x => x) b (snd x) prf)

xplusinverse: (x: Pair) -> (k: NotZero (snd x)) -> Pair
xplusinverse x k = AddRationals x k (AddInverse x k) (xAndInverseNotZero x k)

addinverselemma1: (x: ZZ) -> ((x) + negate (x) = 0)
addinverselemma1 x = plusNegateInverseLZ(x)
