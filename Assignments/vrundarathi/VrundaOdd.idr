module rathivrunda.Odds

import Evens

import Intro

data IsOdd : Nat -> Type where
  OneOdd : IsOdd (S Z)
  SSOdd : (k: Nat)-> (IsOdd k) -> (IsOdd (S (S k)))

threeOdd : IsOdd 3
threeOdd = SSOdd (S Z) OneOdd

twoNotOdd: IsOdd 2 -> Void
twoNotOdd (SSOdd Z OneOdd) impossible
twoNotOdd (SSOdd Z (SSOdd _ _)) impossible

twoEven : IsEven 2
twoEven = SSEven 0 ZEven

SOddEven : (n: Nat) -> (IsOdd n) -> (IsEven (S n))
--SOddEven (S Z) (OneOdd) = twoEven
--SOddEven (S (S k)) (SSOdd k x) = SSEven (S k) (SOddEven k x)
SOddEven (S Z) OneOdd = SSEven 0 ZEven
SOddEven (S (S k)) (SSOdd k x) = SSEven (S k) (SOddEven k x)



SEvenOdd : (n: Nat) -> (IsEven n) -> (IsOdd (S n))
SEvenOdd Z(ZEven) =  (OneOdd)
SEvenOdd (S (S k)) (SSEven k x) = SSOdd (S k) (SEvenOdd k x)


nOddOrEven : (n: Nat) -> Either (IsEven n) (IsOdd n)
nOddOrEven Z = Left ZEven
nOddOrEven (S k) = case (nOddOrEven k) of
                       (Left l) => Right (SEvenOdd k l)
                       (Right r) => Left (SOddEven k r)


nNotBothOddEven : (n: Nat) -> (IsEven n) -> (IsOdd n) -> Void
nNotBothOddEven Z ZEven OneOdd impossible
nNotBothOddEven Z ZEven (SSOdd _ _) impossible
nNotBothOddEven (S (S k)) (SSEven k x) (SSOdd k y) = nNotBothOddEven k x y



SumEven : (n : Nat) -> (IsOdd n) -> (m :  Nat) -> (IsOdd m) -> (IsEven (add m n))
SumEven (S Z) OneOdd (S Z) OneOdd = twoEven
SumEven (S Z) OneOdd (S (S k)) (SSOdd k x) = SSEven (S k) (SOddEven k x)
SumEven (S (S k)) (SSOdd k x) m y = SSEven (add k m) SumEven k m


xyz : (f : Nat -> Nat) -> (n : Nat) -> (m : Nat) -> n = m -> f n = f m
xyz f m m (Refl {x = m}) = Refl {x = f m}


OddSdoubleEven : (n: Nat) -> IsOdd n -> (k: Nat ** S (double k) = n)
OddSdoubleEven (S Z) OneOdd = (Z ** Refl {x = 1})
OddSdoubleEven (S (S k)) (SSOdd k x) = step where
  step = case (OddSdoubleEven k x) of
            (m ** pf) => ((S m) ** xyz (\l => S (S l)) (S (double m)) k pf)
