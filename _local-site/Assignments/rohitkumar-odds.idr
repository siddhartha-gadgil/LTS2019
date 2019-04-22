module Rohitkumar.Odds

import Evens

import Intro

{-1-}
public export
data IsOdd : Nat -> Type where
  OneOdd : IsOdd 1
  SSOdd : (n : Nat) -> IsOdd n -> IsOdd (S (S n))
{-2-}
threeIsOdd : IsOdd 3
threeIsOdd = SSOdd (S Z) OneOdd
{-3-}
twonotOdd : IsOdd 2 -> Void
twonotOdd (SSOdd Z OneOdd) impossible
twonotOdd (SSOdd Z (SSOdd _ _)) impossible
{-4-}
nOddThenSnEven : (n : Nat) -> IsOdd n -> IsEven (S n)
nOddThenSnEven (S Z) OneOdd = SSEven Z ZEven
nOddThenSnEven (S (S k)) (SSOdd k x) = SSEven (S k) (nOddThenSnEven k x)
{-5-}
nEvenThenSnOdd : (n : Nat) -> IsEven n -> IsOdd (S n)
nEvenThenSnOdd Z ZEven = OneOdd
nEvenThenSnOdd (S (S k)) (SSEven k x) = SSOdd (S k) (nEvenThenSnOdd k x)
{-6-}
nEitherEvenorOdd : (n : Nat) -> Either (IsEven n) (IsOdd n)
nEitherEvenorOdd Z = Left ZEven
nEitherEvenorOdd (S k) = case (nEitherEvenorOdd k) of
                          (Left l) => Right (nEvenThenSnOdd k l)
                          (Right r) => Left (nOddThenSnEven k r)
{-7-}
nNotEvenandOdd : (n: Nat) -> IsEven n -> IsOdd n -> void
nNotEvenandOdd Z ZEven OneOdd impossible
nNotEvenandOdd Z ZEven (SSOdd _ _) impossible
nNotEvenandOdd (S (S k)) (SSEven k x) (SSOdd k y) = nNotEvenandOdd k x y

{-8-}
nmOddThennmEven : (n : Nat) -> IsOdd n -> (m : Nat) -> IsOdd m -> IsEven (add n m)
nmOddThennmEven (S Z) OneOdd j y = nOddThenSnEven j y
nmOddThennmEven (S (S k)) (SSOdd k x) j y = (SSEven (add k j) (nmOddThennmEven k x j y))
{-9-}
genRefl : (f : (Nat -> Nat)) -> (n : Nat) -> (m : Nat) -> n = m -> f n = f m
genRefl f m m Refl = Refl

halfTheOdd : (n : Nat) -> IsOdd n -> (m : Nat ** ((S (double m)) = n))
halfTheOdd (S Z) OneOdd = (Z ** Refl)
halfTheOdd (S (S k)) (SSOdd k x) = case (halfTheOdd k x) of
                                    (m ** pf) => ((S m) ** (genRefl (\l => S (S l)) (S (double m)) k pf))
