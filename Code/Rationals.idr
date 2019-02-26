module Rationals

import ZZ

%access public export

Pair : Type
Pair = (Integer, Integer)

ZZPair : Type
ZZPair = (ZZ, ZZ)

ZZtoDb : ZZ -> Double
ZZtoDb x = cast{from=Integer}{to=Double} (cast{from=ZZ}{to=Integer} x)

DbtoZZ : Double -> ZZ
DbtoZZ x = cast{from=Integer}{to=ZZ} (cast{from=Double}{to=Integer} x)


isNotZero : Nat -> Bool
isNotZero Z = False
isNotZero (S k) = True


divides : (m: Integer) -> (n: Integer) -> (k: Integer ** (m * k = n)) -> Integer
divides m n k = (fst k)

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

AddRationals : (x: ZZPair) -> ZZNotZero (snd x) -> (y: ZZPair) -> ZZNotZero (snd y) -> ZZPair
AddRationals x a y b = ((fst x)*(snd y) + (snd x)*(fst y), (snd x)*(snd y))

MultiplyRationals : (x: ZZPair) -> ZZNotZero (snd x) -> (y: ZZPair) -> ZZNotZero (snd y) -> ZZPair
MultiplyRationals x a y b =((fst x)*(fst y), (snd x)*(snd y))

MultInverse : (x: ZZPair) -> ZZNotZero (fst x) -> ZZNotZero (snd x) -> ZZPair
MultInverse x y z = ((snd x), (fst x))

AddInverse : (x: ZZPair) -> ZZNotZero (snd x) -> ZZPair
AddInverse x a = (-(fst x), (snd x))

Subtraction : (x: ZZPair) -> ZZNotZero (snd x) -> (y: ZZPair) -> ZZNotZero (snd y) -> ZZPair
Subtraction x a y b = AddRationals x a (AddInverse y b) b

Division : (x: ZZPair) -> ZZNotZero (snd x) -> (y: ZZPair) -> ZZNotZero (fst y) -> ZZNotZero (snd y) -> ZZPair
Division x a y b c = MultiplyRationals x a (MultInverse y b c) b

--SimplifyRational : (x: Pair) -> NotZero (snd x) -> Pair
--SimplifyRational x a = (divides (gcdab fromIntegerNat((fst x)) fromIntegerNat((snd x))) ___ (fst x), divides (gcdab fromIntegerNat((fst x)) fromIntegerNat((snd x)) __ (snd x))

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

xAndInverseNotZero : (x: ZZPair) -> (k: ZZNotZero (snd x)) -> ZZNotZero (snd (AddInverse x k))
xAndInverseNotZero x (ZZPositiveNotZero (snd x) y) = (ZZPositiveNotZero (snd x) y)

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
