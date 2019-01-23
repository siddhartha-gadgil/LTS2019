module Permutations

import Data.Vect

data IsPer : Vect n Nat -> Vect n Nat -> Type where
  ReflPer : (m : Vect 1 Nat) -> IsPer m m
  HeadPer : IsPer m n -> IsPer a b -> IsPer (m++a) (n++b)
  TailPer : IsPer m n -> IsPer a b -> IsPer (a++m) (b++n)
  MixPer : IsPer m n -> IsPer a b -> IsPer (a++m) (n++b)

data IsSorted : Vect n Nat -> Type where
  ZSorted : IsSorted []
  OSorted : (m : Nat) -> IsSorted [m]
  NextSorted : (m : Nat) -> (prev : Vect (S n) Nat)-> IsSorted prev -> LTE m (head prev) -> IsSorted (m :: prev)

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

Insert: (n : Nat) -> Vect k Nat -> Vect (S k) Nat
Insert n [] = [n]
Insert n (x :: xs) = case (Min n x) of
                        (Left l) => ([n] ++ [x]) ++ xs
                        (Right r) => [x] ++ (Insert n xs)


Sort: (n: Nat) -> Vect n Nat -> (k : Vect n Nat ** IsSorted k)
Sort Z [] = ([] ** ZSorted)
Sort (S Z) [x] = ([x] ** (OSorted x))
Sort (S (S n)) (x :: y :: xs) = ((Insert x (fst (Sort (S n) (y :: xs)))) ** ?ef)
