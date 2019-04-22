module Adithyau.Odds

import Evens

import Intro

data IsOdd : Nat -> Type where
	OneOdd : IsOdd (S Z)
	SSOdd : (k : Nat) -> IsOdd k -> IsOdd (S (S k))

threeOdd : IsOdd 3				{- 3 is odd -}
threeOdd = SSOdd (S Z) OneOdd

twoNotOdd : IsOdd 2 -> Void		{- 2 is not odd -}
twoNotOdd OneOdd impossible
twoNotOdd (SSOdd _ _) impossible

ifOddSEven : (n : Nat) -> (IsOdd n) -> (IsEven (S n))				{- if n is odd, S n is even -}
ifOddSEven (S Z) OneOdd = SSEven 0 ZEven
ifOddSEven (S (S k)) (SSOdd k x) = SSEven (S k) (ifOddSEven k x)

ifEvenSOdd : (n : Nat) -> (IsEven n) -> (IsOdd (S n))				{- if n is even, S n is odd -}
ifEvenSOdd Z ZEven = OneOdd
ifEvenSOdd (S (S k)) (SSEven k x) = SSOdd (S k) (ifEvenSOdd k x)

nOddorEven : (n : Nat) -> Either (IsEven n) (IsOdd n)				{- n is odd or even -}
nOddorEven Z = Left ZEven
nOddorEven (S k) = case (nOddorEven k) of
						(Left l) => Right (ifEvenSOdd k l)
						(Right r) => Left (ifOddSEven k r)

nNotOddandEven : (n : Nat) -> (IsEven n) -> (IsOdd n) -> Void		{- n is not both odd and even -}
nNotOddandEven Z ZEven _ impossible
nNotOddandEven Z (SSEven _ _) _ impossible
nNotOddandEven (S Z) _ OneOdd  impossible
nNotOddandEven (S Z) _ (SSOdd _ _) impossible
nNotOddandEven (S (S k)) ZEven _ impossible
nNotOddandEven (S (S k)) (SSEven k x) OneOdd impossible
nNotOddandEven (S (S k)) (SSEven k x) (SSOdd k y) = nNotOddandEven k x y

isEvenAdd : (n : Nat) -> (m : Nat) -> (IsOdd n) -> (IsOdd m) -> (IsEven (add n m))				{- if n and m are odd, add n m is even -}
isEvenAdd (S Z) k OneOdd x = ifOddSEven k x
isEvenAdd (S (S k)) l (SSOdd k proofk) proofl = SSEven (add k l) (isEvenAdd k l proofk proofl)

isDoubleS : (n : Nat) -> (IsOdd n) -> (m : Nat ** n = S (double m))					{- if n is odd, there exists an m such that n = S (double m) -}
isDoubleS (S Z) OneOdd = (Z ** Refl)
isDoubleS (S (S k)) (SSOdd k x) = step where
	step = case (isDoubleS k x) of
				(m ** pf) => ((S m) ** apNat (\l => S (S l)) k (S (double m)) pf)
