module Bezout

import Data.Vect
import Data.Fin
import ZZ

%access public export

gcdAux: (n: Nat) -> (m: Nat) -> (LTE m n) -> Nat
gcdAux n Z LTEZero = n
gcdAux (S right) (S left) (LTESucc x) = ?EuclidIndAux_rhs_2

switchLTE : (n: Nat) -> (m: Nat) -> (contra : (LTE n m) -> Void) -> LTE m n
switchLTE Z m contra = void (contra (the (LTE Z m) LTEZero))
switchLTE (S k) Z contra = LTEZero
switchLTE (S k) (S j) contra = ?switchLTE_rhs_3


{-Copied from Chinmaya's code. Gives quotient and remainder on divison-}
{-This just computes the qoutient and the remainder, but it doesn't prove that they indeed satisfy the conditions a = b*q + r and r < b -}
Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat)
Eucl Z b = (Z,Z)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False =>
                      (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True =>
                      (Z, S k)
{-Just a slight modification of the Euclid's division function to give the remainder -}
rem : (a : Nat) -> (b : Nat) -> Nat
rem Z b = Z
rem (S k) b = case (lte (S (S k)) b) of
                    False => (rem (minus (S k) b) b)
                    True => (S k)
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
returnab (a ,b ,c ,d, e ,f)  = ((cast c),(cast e))
{-Returns the Bezout coefficients-}
Bezout : Nat ->Nat -> (ZZ, ZZ)
Bezout k j =  (returnab(Bezouttuple((cast k) , (cast j),1, 0 ,0 ,1)))

{-}
just the functions to compute the GCD in two different ways.

gcd2 : Nat -> Nat -> Nat
gcd2 a b = (cast (((cast a)*(snd (Bezout a b))) + ((cast b)*(fst (Bezout a b)))))

gcdab : Nat -> Nat -> Nat
gcdab b Z = b
gcdab a b = gcdab b (snd (Eucl a b))

All these proofs (except maybe aux2f3) were necessary to avoid various type mismatch errors.
{-}


{-proof of existence of remainders and quotients is necessary to define the concept of divisibilty -}
{-The next step ahead might be to proof the uniqueness of these remainders and quotients probably -}
