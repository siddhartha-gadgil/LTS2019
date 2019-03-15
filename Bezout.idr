module Bezout
import Divisors
import ZZ
import Data.Vect
import Data.Fin
import Rationals
import NatUtils
%access public export




Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat)
Eucl Z b = (Z,Z)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False => (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True => (Z, S k)
{-Improvement on the previous code. is total but without proof-}
{-This just computes the qoutient and the remainder, but it doesn't prove that they indeed satisfy the conditions a = b*q + r and r < b -}
QuotRem : (a: Nat) -> (b: Nat) ->(LTE b a)->(Nat, Nat)
QuotRem a Z LTEZero =(Z,Z)
QuotRem a (S k) x  =  case (isLTE (S k) (minus a (S k))) of
                          Yes pf =>(S( Basics.fst(QuotRem (minus a (S k)) (S k) (pf))),
                                       Basics.snd(QuotRem (minus a (S k)) (S k) (pf)))

                          No contra =>((S Z),(minus a (S k)) )
{-Just a slight modification of the Euclid's division function to give the remainder -}

rem : (a : Nat) -> (b : Nat) -> Nat
rem Z b = Z
rem (S k) b = case (lte (S (S k)) b) of
                    False => (rem (minus (S k) b) b)
                    True => (S k)

{- proof that if p|a and p|b p|a+b -}
LinearisFactor: (p: ZZ) -> (a: ZZ)-> (IsDivisibleZ a p) ->
                          (b: ZZ)-> (IsDivisibleZ b p) -> (IsDivisibleZ (a+b) p)
LinearisFactor p a x b y = plusDiv x y



{-Let rk be the remainder in the Euclidean algorithm at the k-2th step.
Let rk = ak*r0 + bk*r1 where r0 and r1 are the original inputs.Correspondingly  rsk = ask*r0 + bsk*r1 where sk = k+1
Then the I am going to the next step in the Euclid algorithm and changing the coefficients.
These formulas can be easily derived.-}
Euclnos: (Integer,Integer,Integer,Integer,Integer,Integer)->(Integer,Integer,Integer,Integer,Integer,Integer)
Euclnos (rk, rsk ,ak ,ask, bk ,bsk) = (rsk,rssk,ask,assk,bsk,bssk) where
  rssk = cast(snd (Eucl (cast rk) (cast rsk)))
  bssk =bk-bsk* (cast(fst (Eucl (cast rk) (cast rsk))))
  assk =ak-ask* (cast(fst (Eucl (cast rk) (cast rsk))))
{-Does the Euclnos repeatedy until the remainder is zero. Then the previous remainder is the GCD.-}
Bezouttuple: (Integer,Integer,Integer,Integer,Integer,Integer)->(Integer,Integer,Integer,Integer,Integer,Integer)
Bezouttuple (rk, rsk ,ak ,ask, bk, bsk) = case rsk of
                                        0 => (rk, rsk, ak, ask, bk, bsk)
                                        _ => (Bezouttuple (Euclnos (rk ,rsk, ak ,ask ,bk ,bsk)))
{-Returns 2 particular Integers out of a 6 tuple-}
returnab: (Integer,Integer,Integer,Integer,Integer,Integer)->(ZZ,ZZ)
returnab (a ,b ,c ,d, e ,f)  = (cast c,cast e)
{-Returns the Bezout coefficients-}
Bezout : Nat ->Nat ->(ZZ,ZZ)
Bezout k j =  (returnab(Bezouttuple((cast k) , (cast j),1, 0 ,0 ,1)))

|||Same as Euclnos wxcept that it stores the quotient and remainder in a list
MEuclnos:((Integer,Integer,Integer,Integer,Integer,Integer),(List (Integer,Integer)))->((Integer,Integer,Integer,Integer,Integer,Integer),(List (Integer,Integer)))
MEuclnos ((rk, rsk ,ak ,ask, bk ,bsk),xs) = ((Euclnos (rk, rsk ,ak ,ask, bk ,bsk)),((q,r)::xs)) where
  q = (cast(fst (Eucl (cast rk) (cast rsk))))
  r = (cast(snd (Eucl(cast rk) (cast rsk))))
|||Same as Bezouttuple except that it stores the quotient and remainder in a list
MBezout:((Integer,Integer,Integer,Integer,Integer,Integer),(List (Integer,Integer)))->((Integer,Integer,Integer,Integer,Integer,Integer),(List (Integer,Integer)))
MBezout ((rk, rsk ,ak ,ask, bk ,bsk),xs) = case rsk of
                                                0 =>  ((rk, rsk ,ak ,ask, bk ,bsk),xs)
                                                _ =>MBezout (MEuclnos ((rk, rsk ,ak ,ask, bk ,bsk),xs))

|||Gives a list of quotients and remainders in Euclid's Algorithm
EuclList:(a:Nat)->(b:Nat)->List (Integer,Integer)
EuclList a b = (snd (MBezout (((cast a)  ,(cast b), 1,0,0,1),[])))

gcd2 : Nat -> Nat -> ZZ
gcd2 a b = ( (((cast a)*(snd (Bezout a b))) + ((cast b)*(fst (Bezout a b)))))





{-}
just the functions to compute the GCD in two different ways.
{-}
{-
gcd2 : Nat -> Nat -> ZZ
gcd2 a b = ( (((cast a)*(snd (Bezout a b))) + ((cast b)*(fst (Bezout a b)))))
gcdab : Nat -> Nat -> Nat
gcdab b Z = b
gcdab a b = gcdab b (snd (Eucl a b))
{-}
{-proof of existence of remainders and quotients is necessary to define the concept of divisibilty -}
{-The next step ahead might be to proof the uniqueness of these remainders and quotients probably -}
-- defining divisibilty as b | a if there exists q such that a = b*q + Z
-- if b | a and c | b, then c | a.
-- if c | a and c | b, then c | (a + b)
-- auxplusDiv 1 to 4 are just auxilary proofs.
auxtransDiv : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> (b = c*q)
auxtransDiv a b c d = ?auxtransDiv_rhs
auxplusDiv1 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> (a = b) -> (c = d) -> (a + c = b + d)
auxplusDiv1 b b d d Refl Refl = Refl
auxplusDiv2 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (q : Nat) -> (p : Nat) -> (a = c*q) -> (b = c*p) -> (a + b = c*(q + p))
auxplusDiv2 a b c q p pf1 pf2 = (trans (auxplusDiv1 a (c*q) b (c*p) pf1 pf2) (sym(multDistributesOverPlusRight c q p)))
auxplusDiv3 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> (a = c) -> (b = d) -> ((minus a b) = (minus c d))
auxplusDiv3 c d c d Refl Refl = Refl
-- Holes !!
auxplusDiv4 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (q : Nat) -> (p : Nat) -> (a + b = c*q) -> (b = c*p) -> (a = c*(minus q p))
auxplusDiv4 a b c q p pf1 pf2 = ?auxplusDiv3_rhs
--These statements are the two main facts we might be Integererested in.
plusDiv1 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (q : Nat ** a = c*q) -> (p : Nat ** b = c*p) -> (f : Nat ** a + b = c*f)
plusDiv1 a b c (q ** pf1) (p ** pf2) = ((q + p) ** (auxplusDiv2 a b c q p pf1 pf2))
plusDiv2 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (q : Nat ** a + b = c*q) -> (p : Nat ** b = c*p) -> (f : Nat ** a = c*f)
plusDiv2 a b c (q ** pf1) (p ** pf2) = ((minus q p) ** (auxplusDiv4 a b c q p pf1 pf2))
-- I'll try and prove some (possibly useful) facts about the gcd.
-- weak definition of the gcd : d | a, d | b and if c | a and c | b, then c <= d.
--This is the common Factor Type
isCommonFactor : Nat -> Nat -> Nat -> Type
isCommonFactor a b c = ((q : Nat ** a = c*q),(p : Nat ** b = c*p))
--This is the GCD type
-- d is "a" gcd of a and b if isGCD a b d type is inhabited.
-- Uniqueness of GCD not assumed !!
-- the gcd is just assumed to be bigger than any other common divisor, not a multiple of it.
isGCD : Nat -> Nat -> Nat -> Type
isGCD a b d = ((isCommonFactor a b d) , ((c : Nat) -> (isCommonFactor a b c) -> (LTE c d)))
-- try to prove that if d is "a" gcd of (a,b) then it is "a" gcd of (a+b,a)
gcdfact1 : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD a b d) -> (isCommonFactor (a + b) b d)
gcdfact1 a b d (((q ** pf1),(p ** pf2)),f) = ((plusDiv1 a b d (q ** pf1) (p ** pf2)),(p ** pf2))
gcdfact2 : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD a b d) -> (c : Nat) -> (isCommonFactor (a + b) b c) -> (LTE c d)
gcdfact2 a b d (pf , f) c ((q ** pf1),(p ** pf2)) = (f c ((plusDiv2 a b c (q ** pf1) (p ** pf2)),(p ** pf2)))
maingcdfact1 : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD a b d) -> (isGCD (a + b) b d)
maingcdfact1 a b d pf = ((gcdfact1 a b d pf),(gcdfact2 a b d pf))
-- now the proof that if d is "a" gcd of (a+b,b), then it is "a" gcd of (a,b)
gcdfact3 : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD (a + b) b d) -> (isCommonFactor a b d)
gcdfact3 a b d (((q ** pf1),(p ** pf2)),f) = ((plusDiv2 a b d (q ** pf1) (p ** pf2)),(p ** pf2))
gcdfact4 : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD (a + b) b d) -> (c : Nat) -> (isCommonFactor a b c) -> (LTE c d)
gcdfact4 a b d (pf, f) c ((q ** pf1),(p ** pf2)) = (f c ((plusDiv1 a b c (q ** pf1) (p ** pf2)),(p ** pf2)))
maingcdFact2 : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD (a + b) b d) -> (isGCD a b d)
maingcdFact2 a b d pf = ((gcdfact3 a b d pf),(gcdfact4 a b d pf))
-- now the proof that if d is "a" gcd of (a,b), it is also "a" gcd of (b,a)
symCommonFactor : (a : Nat) -> (b : Nat) -> (c : Nat) -> (isCommonFactor a b c) -> (isCommonFactor b a c)
symCommonFactor a b c ((p ** pf1),(q ** pf2)) = ((q ** pf2),(p ** pf1))
symGCD1 : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD a b d) -> ((c : Nat) -> (isCommonFactor b a c) -> (LTE c d))
symGCD1 a b d (pf, f) = g where
                          g c ((p ** pf1),(q ** pf2)) = f c ((q ** pf2),(p ** pf1))
symGCD : (a : Nat) -> (b : Nat) -> (d : Nat) -> (isGCD a b d) -> (isGCD b a d)
symGCD a b d (pf , f) = ((symCommonFactor a b d pf) , (symGCD1 a b d (pf , f)))
-- I'll list the types and functions that might be useful
-- The GCD type : isGCD : Nat -> Nat -> Nat -> Type
--                isGCD a b d = ((isCommonFactor a b d) , ((c : Nat) -> (isCommonFactor a b c) -> (LTE c d)))
-- maingcdfact1 , maingcdfact2 , symGCD.
-- The next step might be to show that the natural number that the euclidian algorithm gives us is indeed a gcd
-- also uniqueness of gcd.
