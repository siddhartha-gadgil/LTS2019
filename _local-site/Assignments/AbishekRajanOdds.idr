module Abishekrajan.Odds

import Evens

import Intro


data IsOdd : Nat -> Type where
  OneOdd : IsOdd 1
  SSOdd : (n : Nat) -> IsOdd n -> IsOdd (S (S n))



threeOdd : IsOdd 3
threeOdd = SSOdd 1 OneOdd



twoNotOdd : IsOdd 2 -> Void
twoNotOdd (SSOdd Z OneOdd) impossible
twoNotOdd (SSOdd Z (SSOdd x y)) impossible



nOddSnEven : (n: Nat) -> IsOdd n -> IsEven (S n)
nOddSnEven (S Z) OneOdd = (SSEven Z ZEven)
nOddSnEven (S (S k)) (SSOdd k x) = SSEven (S k) (nOddSnEven k x)



nEvenSnOdd : (n: Nat) -> IsEven n -> IsOdd (S n)
nEvenSnOdd Z ZEven = OneOdd
nEvenSnOdd (S (S k)) (SSEven k x) = SSOdd (S k) (nEvenSnOdd k x)



nEvenOrOdd : (n: Nat) -> Either (IsEven n) (IsOdd n)
nEvenOrOdd Z = Left ZEven
nEvenOrOdd (S k) = case (nEvenOrOdd k) of
                       (Left l) => Right (nEvenSnOdd k l)
                       (Right r) => Left (nOddSnEven k r)


nNotEvenAndOdd : (n: Nat) -> (IsEven n) -> (IsOdd n) -> Void
nNotEvenAndOdd Z ZEven OneOdd impossible
nNotEvenAndOdd Z ZEven (SSOdd p q) impossible
nNotEvenAndOdd (S (S k)) (SSEven k x) (SSOdd k y) = nNotEvenAndOdd k x y



mOddnOddmplusnEven : (m: Nat) -> IsOdd m -> (n: Nat) -> IsOdd n -> IsEven (add m n)
mOddnOddmplusnEven (S Z) OneOdd (S Z) OneOdd = SSEven 0 ZEven
mOddnOddmplusnEven (S Z) OneOdd (S (S k)) (SSOdd k x) = SSEven (S k) (mOddnOddmplusnEven (S Z) OneOdd k x)
mOddnOddmplusnEven (S (S k)) (SSOdd k x) n y = SSEven (add k n) (mOddnOddmplusnEven k x n y)



apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl

oddIsSDouble : (n: Nat) -> IsOdd n -> (k: Nat ** (S (double k)) = n)
oddIsSDouble (S Z) OneOdd = (0 ** Refl)
oddIsSDouble (S (S k)) (SSOdd k x) = case (oddIsSDouble k x) of
            (m ** y) => ((S m) ** apNat (\l => S (S l)) (S (double m)) k y)
