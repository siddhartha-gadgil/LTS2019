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

given below are the auxilary functions to the proof that given a and b, there exist q and r such that a = b*q + r.
The algorithm above just computes these two numbers, but it doesn't prove that (a = b*q + r and r < b)

f1 is the proof that a + 1 = b*q + (r + 1) given that a = b*q + r

aux1f2 is the proof that given a + 1 <= b, a <= b
aux2f2 is the proof that given a and b, either a <= b or a >= b + 1

aux1f3 is the proof that given a <= b and b <= a, a = b
aux2f3 proves that a = b + c and c = d together imply a = b + d
aux3f3 is the proof that given a = b*c + b, a = b*(c + 1) + 0

All these proofs (except maybe aux2f3) were necessary to avoid various type mismatch errors.
{-}

apNat2 : (a : Nat) -> (b : Nat) -> (a = b) -> (S a = S b)
apNat2 a a Refl = Refl

aux1f2 : (a : Nat) -> (b : Nat) -> (LTE (S a) b) -> (LTE a b)
aux1f2 Z Z LTEZero impossible
aux1f2 Z Z (LTESucc _) impossible
aux1f2 Z (S k) x = LTEZero
aux1f2 (S a) (S k) (LTESucc x) = (LTESucc (aux1f2 a k x))

aux2f2 : (a : Nat) -> (b : Nat) -> (Either (LTE a b) (LTE (S b) a))
aux2f2 Z Z  = Left LTEZero
aux2f2 Z (S b) = Left LTEZero
aux2f2 (S k) Z = Right (LTESucc LTEZero)
aux2f2 (S k) (S b) = step where
                  step = case (aux2f2 k b) of
                    (Left l) => (Left (LTESucc l))
                    (Right r) => (Right (LTESucc r))

f1 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a = b + c) -> ((S a) = b + (S c))
f1 a c k pf = (trans (apNat2 a (c + k) pf) (plusSuccRightSucc c k))

aux1f3 : (a : Nat) -> (b : Nat) -> (LTE a b) -> (LTE b a) -> (a = b)
aux1f3 Z Z LTEZero LTEZero = Refl
aux1f3 Z (S _) LTEZero LTEZero impossible
aux1f3 Z (S _) LTEZero (LTESucc _) impossible
aux1f3 (S _) Z LTEZero LTEZero impossible
aux1f3 (S _) Z (LTESucc _) LTEZero impossible
aux1f3 (S k) (S j) (LTESucc x) (LTESucc y) = (apNat2 k j (aux1f3 k j x y))

aux2f3 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) -> (a = b + c) -> (c = d) -> (a = b + d)
aux2f3 a b Z Z prf Refl = prf
aux2f3 _ _ Z (S _) _ Refl impossible
aux2f3 _ _ (S _) Z _ Refl impossible
aux2f3 (b + (S j)) b (S j) (S j) Refl Refl = Refl


aux3f3 : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a = (b*c) + b) -> (a = b*(S c) + Z)
aux3f3 a b k prf = (trans (trans (trans (prf) (plusCommutative (b*k) b)) (sym (multRightSuccPlus b k))) (sym (plusZeroRightNeutral (b*(S k)))))

{-Caveat : the function elemproof hasn't been programmed for the divisor b being equal to zero -}
{-replacig b with (S b) everywhere in the proof has been done to avoid the case b = 0-}

elemproof1 : (a : Nat) -> (b : Nat) -> (x : (Nat, Nat) ** ((a = (b*(fst x)) + (snd x)) , (LTE (S (snd x)) b)))
elemproof1 Z (S b) = ((0,0) ** ((sym (trans (trans (plusCommutative ((S b)*Z) Z) (sym (multLeftSuccPlus (S b) Z))) (multZeroRightZero (S (S b))))), (LTESucc LTEZero)))
elemproof1 (S k) (S b) = step where
                     step = case (elemproof1 k (S b)) of
                       ((q,r) ** (pf , pff)) => case (aux2f2 (S (S r)) (S b)) of
                                                  Left l => ((q , (S r)) ** ((f1 k ((S b)*q) r pf) , l))
                                                  Right (LTESucc ri) => (((S q) , Z) ** ((aux3f3 (S k) (S b) q (aux2f3 (S k) ((S b)*q) (S r) (S b) (f1 k ((S b)*q) r pf) (aux1f3 (S r) (S b) pff ri))) , (LTESucc LTEZero)))

{-proof of existence of remainders and quotients is necessary to define the concept of divisibilty -}
{-The next step ahead might be to proof the uniqueness of these remainders and quotients probably -}
