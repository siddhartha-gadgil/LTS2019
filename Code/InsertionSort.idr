module InsertionSort

import Data.Vect
import Data.Fin
import Permutation
import PermCons
import Finite
import DecOrderNat
import LTE_Properties
import SortingWithProof

%access public export
%default total

Smaller : Nat -> Nat -> Nat
Smaller Z n = Z
Smaller  m Z = Z
Smaller  (S m) (S n) = (S (Smaller m n))

-----------------------------------------------------------------

Min : (m: Nat) -> (n: Nat) -> Either (LTE m n) (LTE n m)
Min Z n = Left LTEZero
Min m Z = Right LTEZero
Min (S a) (S b) = case (Min a b) of
                       (Left l) => Left (LTESucc l)
                       (Right r) => Right (LTESucc r)

-----------------------------------------------------------------

insert: (k: Nat) -> (Vect n Nat) -> (Vect (S n) Nat)
insert k Nil = k :: Nil
insert k (x :: xs) = case (decMin k x) of
    (Left pf) => k :: x :: xs
    (Right pf) => x :: (insert k xs)

-----------------------------------------------------------------

sort : (Vect n Nat) -> (Vect n Nat)
sort [] = []
sort (x :: xs) = insert x (sort xs)

-----------------------------------------------------------------

VectMin: (n: Nat) -> (Vect n Nat) -> Nat
VectMin Z [] = Z
VectMin (S Z) [k] = k
VectMin (S (S len)) (x :: xs) = Smaller (VectMin (S len) xs) (x)

-----------------------------------------------------------------



CheckSortedVect : (n: Nat) -> (Vect n Nat) -> Bool
CheckSortedVect Z [] = True
CheckSortedVect (S Z) [k] = True
CheckSortedVect (S (S n)) (x :: xs) = case (isLTE x (VectMin (S n) xs)) of
                                         (Yes prf) => (CheckSortedVect (S n) xs)
                                         (No contra) => False
