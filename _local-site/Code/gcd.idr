module gcd

import ZZ
import Bezout

--isDivisible a b can be constucted if b divides a
isDivisible : Nat -> Nat -> Type
isDivisible a b = (n : Nat ** a = b * n)

--1 divides everything
oneDiv : (a : Nat) -> isDivisible a 1
oneDiv a = (a ** rewrite plusZeroRightNeutral a in Refl)

--If 1|a => 1*c | a*c
mulDiv : (a, c : Nat) -> isDivisible a 1 -> isDivisible (a * c) c
mulDiv a c x = (a ** rewrite multCommutative c a in Refl)

gcdBya : (a : Nat) -> (b : Nat) -> NotBothZero a b -> Nat
gcdBya a b prf = div a (gcd a b {ok=prf})

gcdByb : (a : Nat) -> (b : Nat) -> NotBothZero a b -> Nat
gcdByb a b prf = div b (gcd a b {ok=prf})

|||Genetes a proof of (a+b) = d*(n+m) from (a=d*n)and (b=d*m)
DistributeProof: (a:Nat)->(b:Nat)->(d:Nat)->(n:Nat)->(m:Nat)->(a=d*n)->(b=d*m)->((a+b) = d*(n+m))
DistributeProof a b d n m pf1 pf2 = rewrite  (multDistributesOverPlusRight d n m) in(trans (the (a+b=(d*n)+b) (v1)) v2) where
  v1 =plusConstantRight a (d*n) b pf1
  v2 =plusConstantLeft b (d*m) (d*n) pf2
  
|||The theorem d|a =>d|ac
MultDiv:(isDivisible a d) ->(c:Nat)->(isDivisible (a*c) d)
MultDiv {d} (n**Refl) c =((n*c)** (rewrite sym (multAssociative d n c) in (Refl)))

|||The theorem d|a and d|b =>d|(a+b)
PlusDiv : (isDivisible a d)->(isDivisible b d)->(isDivisible (a+b) d)
PlusDiv {d}{a}{b} (n**prf1) (m**prf2) = ((n+m)**(DistributeProof a b d n m prf1 prf2))
{-

gcdDiva : (a : Nat) -> (b : Nat) -> NotBothZero a b -> isDivisible a (gcd a b)
gcdDiva a b prf = mulDiv (gcdBya a b prf)
  (gcd a b {ok=prf})
  (oneDiv (gcdBya a b prf))
-}
{-
gcdDivb : (a : Nat) -> (b : Nat) -> NotBothZero a b -> isDivisible b (gcd a b)
gcdDivb a b prf = mulDiv (gcdByb a b prf)
  (gcd a b {ok=prf})
  (oneDiv (gcdByb a b prf))
-}
--gcd is already implemented in the standard library
gcdproof : (a : Nat) -> (b : Nat) -> NotBothZero a b ->
  (d : Nat ** ((k : Nat ** a = d*k),(l : Nat ** b = d*l)))
gcdproof a b prf =
  (gcd a b {ok=prf} ** (?parta, ?partb))

--Bezout
{-
--if gcd a b = d, d = ax + by for some x,y Integers (Given by Bezout)
bezproof : (a : Nat) -> (b : Nat) -> NotBothZero a b ->
  (x : (ZZ,ZZ) ** ((cast{from=Nat}{to=ZZ} a)*(fst x) +
                   (cast{from=Nat}{to=ZZ} b)*(snd x) = cast (gcd a b)))
bezproof a b x = (Bezout a b ** ?help)
-}
