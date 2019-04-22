module Chinmaya.Odds

import Intro
import Evens

-- Q.1.
data IsOdd: Nat -> Type where
  SZOdd: IsOdd (S Z)
  SSOdd: (n: Nat) -> IsOdd (n) -> IsOdd (S (S n))

-- Q.2.
threeOdd: IsOdd 3
threeOdd = SSOdd 1 SZOdd

-- Q.3.
twoNotOdd: IsOdd 2 -> Void
twoNotOdd (SSOdd Z SZOdd) impossible
twoNotOdd (SSOdd Z (SSOdd _ _)) impossible

-- Q.4.
nOddSnEven: (n: Nat) -> IsOdd n -> IsEven (S n)
nOddSnEven (S Z) SZOdd = SSEven Z ZEven
nOddSnEven (S (S k)) (SSOdd k x) = SSEven (S k) (nOddSnEven(k)(x))

-- Q.5.
nEvenSnOdd: (n: Nat) -> IsEven n -> IsOdd (S n)
nEvenSnOdd Z ZEven = SZOdd
nEvenSnOdd (S (S k)) (SSEven k x) = SSOdd (S k) (nEvenSnOdd(k)(x))

-- Q.6.
nEvenorOdd: (n: Nat) -> Either(IsEven n)(IsOdd n)
nEvenorOdd Z = Left(ZEven)
nEvenorOdd (S k) = case (nEvenorOdd k) of
                      Left l => Right(nEvenSnOdd k l)
                      Right r => Left(nOddSnEven k r)

-- Q.7.
nNotBoth: (n: Nat) -> IsEven n -> IsOdd n -> Void
nNotBoth (S Z) ZEven SZOdd impossible
nNotBoth (S Z) (SSEven _ _) SZOdd impossible
nNotBoth (S (S k)) (SSEven k x) (SSOdd k y) = nNotBoth k x y

-- Q.8.
addnmOdd: (n: Nat) -> (m: Nat) -> IsOdd n -> IsOdd m -> IsEven (add n m)
addnmOdd (S Z) m SZOdd y = nOddSnEven m y
addnmOdd (S (S k)) m (SSOdd k x) y = SSEven (add k m) (addnmOdd k m x y)

-- double wasn't loading somehow, so copy-pasted def from Intro
-- double: Nat -> Nat
-- double Z = Z
-- double (S k) = S (S (double k))

-- auxiliary Sequal function
Sequal: {n: Nat} -> {m: Nat} -> (n = m) -> (S n = S m)
Sequal Refl = Refl

-- Q.9.
nSdoublem: (n: Nat) -> IsOdd n -> (DPair Nat (\m => (n = S(double(m)))))
nSdoublem (S Z) SZOdd = (Z ** Refl)
nSdoublem (S (S k)) (SSOdd k x) = (S(fst(nSdoublem k x))** Sequal(Sequal(snd(nSdoublem k x))))
