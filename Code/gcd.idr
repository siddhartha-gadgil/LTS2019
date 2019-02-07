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
{-}

gcdDiva : (a : Nat) -> (b : Nat) -> NotBothZero a b -> isDivisible a (gcd a b)
gcdDiva a b prf = mulDiv (gcdBya a b prf)
  (gcd a b {ok=prf})
  (oneDiv (gcdBya a b prf))

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
