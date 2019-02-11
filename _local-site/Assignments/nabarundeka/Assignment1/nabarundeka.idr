module nabarundeka.Odds

import Evens

import Intro


data IsOdd : (n : Nat) -> Type where
  OneOdd : IsOdd 1
  SSOdd : (n : Nat) -> IsOdd n -> IsOdd (S (S n))

threeOdd : IsOdd 3
threeOdd = SSOdd 1 OneOdd

twoNotOdd : IsOdd 2 -> Void
twoNotOdd OneOdd impossible
twoNotOdd (SSOdd Z OneOdd) impossible
twoNotOdd (SSOdd Z (SSOdd _ _)) impossible

nOddSnEven : (n : Nat) -> IsOdd n -> IsEven (S n)
nOddSnEven (S Z) OneOdd = SSEven 0 ZEven
nOddSnEven (S (S n)) (SSOdd n x) = SSEven (S n) (nOddSnEven n x)

nEvenSnOdd : (n : Nat) -> IsEven n -> IsOdd (S n)
nEvenSnOdd Z ZEven = OneOdd
nEvenSnOdd (S (S n)) (SSEven n x) = SSOdd (S n) (nEvenSnOdd n x)

nOddOrEven : (n : Nat) -> Either (IsEven n) (IsOdd n)
nOddOrEven Z = Left ZEven
nOddOrEven (S n) = case (nOddOrEven n) of
                      (Left l) => Right (nEvenSnOdd n l)
                      (Right r) => Left (nOddSnEven n r)

nNotOddEven : (n: Nat) -> (IsOdd n) -> (IsEven n) -> Void
nNotOddEven Z OneOdd ZEven impossible
nNotOddEven (S Z) OneOdd ZEven impossible
nNotOddEven (S (S n)) (SSOdd n x) (SSEven n y) = nNotOddEven n x y

nNotOddEvenBoth : (n : Nat) -> (IsOdd n, IsEven n) -> Void
nNotOddEvenBoth n (x,y) = nNotOddEven n x y

sumOddOdd : (n : Nat) -> (m : Nat) -> (IsOdd n) -> (IsOdd m) -> IsEven (add n m)
sumOddOdd (S Z) m OneOdd x = nOddSnEven m x
sumOddOdd (S (S n)) m (SSOdd n x) y = SSEven (add n m) (sumOddOdd n m x y)

apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl

succOddDivByTwo : (n : Nat) -> IsOdd n -> (k : Nat ** (S(double k)) = n)
succOddDivByTwo (S Z) OneOdd = (Z ** Refl)
succOddDivByTwo (S (S k)) (SSOdd k x) = step where
  step = case (succOddDivByTwo k x) of
              (m ** pf) => ((S m) ** apNat (\l=> S (S l)) (S(double m)) k pf)
