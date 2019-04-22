module PiyushSati.Odds

import Evens

import Intro

--Answer 1
data IsOdd : Nat -> Type where
  OneOdd : IsOdd (S Z)
  SSOdd : (n: Nat) -> IsOdd n -> IsOdd (S(S n))

--Answer 2
ThreeOdd : IsOdd 3
ThreeOdd = SSOdd 1 OneOdd

--Answer 3
TwoEven: IsOdd 2-> Void
TwoEven OneOdd impossible
TwoEven (SSOdd _ _) impossible

--Answer 5

nEvenSnOdd: (n: Nat) -> IsEven n -> IsOdd (S n)
nEvenSnOdd Z ZEven = OneOdd
nEvenSnOdd (S (S n)) (SSEven n nEven) = SSOdd (S n) (nEvenSnOdd n nEven)



--Answer 4

nOddSnEven: (n: Nat) -> IsOdd n -> IsEven (S n)
nOddSnEven (S Z) OneOdd = SSEven Z ZEven
nOddSnEven (S (S n)) (SSOdd n nOdd) = SSEven (S n) (nOddSnEven n nOdd)



--Answer 6

nEvenOrOdd : (n: Nat) -> Either (IsEven n) (IsOdd n)
nEvenOrOdd Z = Left ZEven
nEvenOrOdd (S Z) = Right OneOdd
nEvenOrOdd (S n) =  case (nEvenOrOdd n) of
                       (Left nEven) => Right (nEvenSnOdd n nEven)
                       (Right nOdd) => Left (nOddSnEven n nOdd)



--Answer 7

nEvenAndOdd : (n: Nat) -> IsEven n -> IsOdd n -> Void
nEvenAndOdd Z ZEven OneOdd impossible
nEvenAndOdd (S Z) (SSEven _ _) OneOdd impossible
nEvenAndOdd (S (S n)) (SSEven n x) (SSOdd n y) = nEvenAndOdd n x y


--Answer 8

SumTwoOdd : (n: Nat) -> (m: Nat) -> IsOdd n -> IsOdd m -> IsEven (add n m)
SumTwoOdd (S Z) m OneOdd mOdd = (nOddSnEven m mOdd)
SumTwoOdd (S (S n)) m (SSOdd n nOdd) mOdd = SSEven (add n m) (SumTwoOdd n m nOdd mOdd)

--
apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl

--Answer 9

MinusOneByTwo : (n: Nat) -> IsOdd n -> (m: Nat ** S (double m) = n)
MinusOneByTwo (S Z) OneOdd = (Z **Refl)
MinusOneByTwo (S (S n)) (SSOdd n nOdd) = step where
  step = case (MinusOneByTwo n nOdd) of
            (m ** x) => ((S m) ** apNat (\l => S (S l)) (S(double m)) n x)
