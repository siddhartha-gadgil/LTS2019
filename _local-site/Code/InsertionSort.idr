module InsertionSort

import Data.Vect

Smaller : Nat -> Nat -> Nat
Smaller Z n = Z
Smaller  m Z = Z
Smaller  (S m) (S n) = (S (Smaller m n))

Min : (m: Nat) -> (n: Nat) -> Either (LTE m n) (LTE n m)
Min Z n = Left LTEZero
Min m Z = Right LTEZero
Min (S a) (S b) = case (Min a b) of
                       (Left l) => Left (LTESucc l)
                       (Right r) => Right (LTESucc r)

Insert: (k: Nat) -> (Vect n Nat) -> (Vect (S n) Nat)
Insert k [] = [k]
Insert k (x :: xs) = case (Min k x) of
                        (Left l) => ([k] ++ [x]) ++ xs
                        (Right r) => [x] ++ (Insert k xs)


Sort: (Vect n Nat) -> (Vect n Nat)
Sort [] = []
Sort (x :: xs) = Insert x (Sort xs)

VectMin: (n: Nat) -> (Vect n Nat) -> Nat
VectMin Z [] = Z
VectMin (S Z) [k] = k
VectMin (S (S len)) (x :: xs) = Smaller (VectMin (S len) xs) (x)


CheckSortedVect : (n: Nat) -> (Vect n Nat) -> Bool
CheckSortedVect Z [] = True
CheckSortedVect (S Z) [k] = True
CheckSortedVect (S (S n)) (x :: xs) = case (isLTE x (VectMin (S n) xs)) of
                                         (Yes prf) => (CheckSortedVect (S n) xs)
                                         (No contra) => False
