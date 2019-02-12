module Bezout


import Data.Vect
import Data.Fin

{-Copied from Chinmay's code. Gives quotient and remainder on divison-}
Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat)
Eucl Z b = (0,0)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False => (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True => (0, S k)



{-Let rk be the remainder in the Euclidean algorithm at the k-2th step.
Let rk = ak*r0 + bk*r1 where r0 and r1 are the original inputs.Correspondingly  rsk = ask*r0 + bsk*r1 where sk = k+1
Then the I am going to the next step in the Euclid algorithm and changing the coefficients.
These formulas can be easily derived.-}
Euclnos: (Int,Int,Int,Int,Int,Int)->(Int,Int,Int,Int,Int,Int)
Euclnos (rk, rsk ,ak ,ask, bk ,bsk) = (rsk,rssk,ask,assk,bsk,bssk) where
  rssk = cast(snd (Eucl (cast rk) (cast rsk)))
  bssk =bk-bsk* (cast(fst (Eucl (cast rk) (cast rsk))))
  assk =ak-ask* (cast(fst (Eucl (cast rk) (cast rsk))))
{-Does the Euclnos repeatedy until the remainder is zero. Then the previous remainder is the GCD.-}
Bezouttuple: (Int,Int,Int,Int,Int,Int)->(Int,Int,Int,Int,Int,Int)
Bezouttuple (rk, rsk ,ak ,ask, bk, bsk) = case rsk of
                                        0 => (rk, rsk, ak, ask, bk, bsk)
                                        _ => (Bezouttuple (Euclnos (rk ,rsk, ak ,ask ,bk ,bsk)))
{-Returns 2 particular integers out of a 6 tuple-}
returnab: (Int,Int,Int,Int,Int,Int)->(Int,Int)
returnab (a ,b ,c ,d, e ,f)  = (c,e)
{-Returns the Bezout coefficients-}
Bezout : Nat ->Nat ->(Int, Int)
Bezout k j =  (returnab(Bezouttuple((cast k) , (cast j),1, 0 ,0 ,1)))

