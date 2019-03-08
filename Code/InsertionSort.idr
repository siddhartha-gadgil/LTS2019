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
    (left pf) => k :: x :: xs
    (right pf) => x :: (insert k xs)

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

insertHelper1 : (n : Nat) -> (a, x : Nat) -> 
                (xs : (Vect n Nat)) -> (LTE a x) ->
                (IsSorted (S n) (x :: xs) ) ->
                (IsSorted (S (S n)) (a :: x :: xs) )
                
insertHelper1 Z a x Nil pfLTE pfSort FZ = (LTE_Property1 a)
insertHelper1 Z a x Nil pfLTE pfSort (FS FZ) = pfLTE
insertHelper1 (S k) a x xs pfLTE pfSort FZ = (LTE_Property1 a)
insertHelper1 (S k) a x xs pfLTE pfSort (FS FZ) = pfLTE
insertHelper1 (S k) a x xs pfLTE pfSort (FS (FS l)) = 
    pfSort (FS l)
    
-----------------------------------------------------------------
{-
insertHelper2 : (n : Nat) -> (a, x : Nat) -> 
                (xs : (Vect n Nat)) -> (LTE x a) ->
                (IsSorted (S n) (x :: xs) ) ->
                (IsSorted (S (S n)) (x :: a :: xs) )

insertHelper2 Z a x Nil pfLTE pfSort FZ = (LTE_Property1 x)
insertHelper2 Z a x Nil pfLTE pfSort (FS FZ) = pfLTE
insertHelper2 (S k) a x xs pfLTE pfSort FZ = (LTE_Property1 x)                    
insertHelper2 (S k) a x xs pfLTE pfSort (FS FZ) = pfLTE
insertHelper2 (S k) a x (y :: xs) pfLTE pfSort (FS (FS FZ)) = 
    LTE_Property2 x a y pfLTE (pfSort (FS FZ))

insertHelper2 (S k) a x (y :: xs) pfLTE pfSort (FS (FS (FS l))) =
    pfSort (FS (FS l))    
-}        
 
-----------------------------------------------------------------

insertProof : (n : Nat) -> (a : Nat) -> (xs : Vect n Nat) -> 
              (IsSorted n xs) ->
              (IsSorted (S n) (insert a xs)) 

insertProof Z a Nil pf = fun where
    fun : (k : Fin (S Z)) -> 
          (LTE (index (pred k) (a :: Nil)) (index k (a :: Nil)))
    fun FZ = (LTE_Property1 a)
    fun (FS k) impossible

insertProof (S k) a (x :: xs) fun = case (decMin a x) of
    (left pfMin) => ?rhs_last_1  
    (right pfMin) => ?rhs_last

-----------------------------------------------------------------


sortProof : (n : Nat) -> (Vect n Nat) -> 
            (v : (Vect n Nat) ** (IsSorted n v))
sortProof Z Nil = (Nil ** fun) where
    fun : (IsSorted Z Nil) 
    fun elem impossible
    
-----------------------------------------------------------------



CheckSortedVect : (n: Nat) -> (Vect n Nat) -> Bool
CheckSortedVect Z [] = True
CheckSortedVect (S Z) [k] = True
CheckSortedVect (S (S n)) (x :: xs) = case (isLTE x (VectMin (S n) xs)) of
                                         (Yes prf) => (CheckSortedVect (S n) xs)
                                         (No contra) => False
