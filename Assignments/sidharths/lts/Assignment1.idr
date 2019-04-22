module Sidharths.Odds

import Evens

import Intro

data IsOdd : Nat -> Type where
  OneOdd : IsOdd 1
  SSOdd : (n: Nat) -> IsOdd n -> IsOdd (S (S n))

ThreeOdd : IsOdd 3
ThreeOdd = SSOdd 1 OneOdd

TwoOdd : IsOdd 2 -> Void
TwoOdd OneOdd impossible
TwoOdd (SSOdd _ _) impossible

NOddSnEven : (n : Nat) -> (IsOdd n) -> (IsEven (S n))
NOddSnEven (S Z) OneOdd = twoEven
NOddSnEven (S (S k)) (SSOdd k x) = (SSEven (S k) (NOddSnEven k x))

NEvenSnOdd : (n : Nat) -> (IsEven n) -> (IsOdd (S n))
NEvenSnOdd Z ZEven = OneOdd
NEvenSnOdd (S (S k)) (SSEven k x) = (SSOdd (S k)) (NevenSnOdd k x))

NEvenorOdd : (n : Nat) -> Either (IsEven n) (IsOdd n)
NEvenorOdd Z = Left ZEven
NEvenorOdd (S k) = case (NEvenorOdd k) of
                        (Left l) => Right (NEvenSnOdd k l)
                        (Right r) => Left (NOddSnEven k r)


NnotbothOddEven : (n : Nat) -> (IsEven n) -> (IsOdd n) -> Void
NnotbothOddEven Z ZEven OneOdd impossible
NnotbothOddEven (S (S k)) (SSEven k x) (SSOdd k y) = NnotbothOddEven k x y

AddEven : (n : Nat) -> (m : Nat) -> IsOdd n -> IsOdd m -> IsEven (add n m)
AddEVen (S Z) m OneOdd x = NOddSnEven m x
AddEven (S (S k)) m (SSOdd k x) y = SSEVen (add k m) (AddEven k m x y)

NOddHalf : (n : Nat) -> IsOdd n -> Nat
NOddHalf (S Z) OneOdd = Z
NOddHalf (S (S k)) (SSOdd k x) = S (NOddHalf k x)
