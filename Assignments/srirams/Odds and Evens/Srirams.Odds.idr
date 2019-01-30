module Srirams.Odds
-- S.Sriram (14487)

import Evens

import Intro

-- 1 --
data IsOdd : Nat -> Type where
  OOdd : IsOdd 1
  SSOdd : (x : Nat) -> (IsOdd x) -> IsOdd (S (S x))

-- 2 --
threeOdd : IsOdd 3
threeOdd = SSOdd 1 OOdd

-- 3 --
twoOdd : IsOdd 2 -> Void
twoOdd (SSOdd Z OOdd) impossible
twoOdd (SSOdd Z (SSOdd _ _)) impossible

-- 4 --
nOddSnEven : (n : Nat) -> (IsOdd n) -> (IsEven (S n))
nOddSnEven (S Z) OOdd = SSEven 0 ZEven
nOddSnEven (S (S x)) (SSOdd x y) = SSEven (S x) (nOddSnEven x y)

-- 5 --
nEvenSnOdd : (n : Nat) -> (IsEven n) -> (IsOdd (S n))
nEvenSnOdd Z ZEven = OOdd
nEvenSnOdd (S (S x)) (SSEven x y) = SSOdd (S x) (nEvenSnOdd x y)

-- 6 --
nEvenOrOdd : (n : Nat) -> Either (IsEven n) (IsOdd n)
nEvenOrOdd Z = Left ZEven
nEvenOrOdd (S k) = case (nEvenOrOdd k) of
                        (Left l) => Right (nEvenSnOdd k l)
                        (Right r) => Left (nOddSnEven k r)

-- 7 --
nNotBothEandO : (n : Nat) -> IsEven n -> IsOdd n -> Void
nNotBothEandO Z ZEven OOdd impossible
nNotBothEandO Z ZEven (SSOdd _ _) impossible
nNotBothEandO (S (S k)) (SSEven k x) (SSOdd k y) = nNotBothEandO k x y

-- 8 --
nmOddaddEven : (n : Nat) -> IsOdd n -> (m: Nat) -> IsOdd m -> IsEven (add n m)
nmOddaddEven (S Z) OOdd (S Z) OOdd = SSEven 0 ZEven
nmOddaddEven (S Z) OOdd (S (S x)) (SSOdd x y) = SSEven (S x) (nOddSnEven x y)
nmOddaddEven (S (S x)) (SSOdd x z) m y = (nOddSnEven (S (add x m)) (nEvenSnOdd (add x m) (nmOddaddEven x z m y)))

-- Auxillary --
aux : (f : Nat -> Nat) -> (n : Nat) -> (m : Nat) -> n = m -> f n = f m
aux f m m (Refl {x = m}) = Refl {x = f m}

-- 9 --
minuOnebyTwo : (n: Nat) -> IsOdd n -> (k: Nat ** S (double k) = n)
minuOnebyTwo (S Z) OOdd = (Z ** Refl {x = 1})
minuOnebyTwo (S (S k)) (SSOdd k x) = step where
  step = case (minuOnebyTwo k x) of
            (m ** pf) => ((S m) ** aux (\l => S (S l)) (S (double m)) k pf)
