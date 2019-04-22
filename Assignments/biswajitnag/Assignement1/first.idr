module biswajitnag.Odds

import Evens

import Intro

-- Define an inductive type family IsOdd : Nat -> Type such that IsOdd n is inhabited if and only if n is odd.

data IsOdd : Nat -> Type where
  OneOdd : IsOdd 1
  SSOdd : (n: Nat) -> IsOdd n -> IsOdd ( S ( S ( n ) ) )

-- Show that 3 is odd.

Q2: IsOdd 3
Q2 = SSOdd 1 OneOdd

-- Show that 2 is not odd.

Q3: IsOdd 2 -> Void
Q3 (SSOdd Z OneOdd) impossible
Q3 (SSOdd Z (SSOdd _ _)) impossible

-- Show that if n: Nat is odd, then its successor S n is even.

Q4: (n: Nat) -> IsOdd n -> IsEven (S n)
Q4 (S Z) OneOdd = SSEven Z ZEven
Q4 (S (S n)) (SSOdd n x) = SSEven (S n) (Q4 n x)

-- Show that if n: Nat is even, then its successor S n is odd.

Q5: (n: Nat) -> IsEven n -> IsOdd (S n)
Q5 Z ZEven = OneOdd
Q5 (S (S n)) (SSEven n x) = SSOdd (S n) (Q5 n x)

-- Show that every number n : Nat is either even or odd.

Q6: (n: Nat) -> Either (IsEven n) (IsOdd n)
Q6 Z = Left ZEven
Q6 (S k) = case (Q6 k) of
                (Left l) => Right (Q5 k l)
                (Right r) => Left (Q4 k r)

-- Show that no number n: Nat is both even and odd.

Q7: (n: Nat) -> IsEven n -> IsOdd n -> Void
Q7 Z ZEven OneOdd impossible
Q7 Z ZEven (SSOdd _ _) impossible
Q7 (S (S k)) (SSEven k x) (SSOdd k y) = Q7 k x y

-- Show that if n: Nat and m: Nat are odd, then add n m is even (here add is from the intro).

Q8: (n: Nat) -> IsOdd n -> (m: Nat) -> IsOdd m -> IsEven (add n m)
Q8 (S Z) OneOdd m y = Q4 m y
Q8 (S (S k)) (SSOdd k x) m y = SSEven (add k m) (Q8 k x m y)

-- Show that if n: Nat is odd, then there exists m: Nat such that n = S (double m).

apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl

Q9: (n: Nat) -> IsOdd n -> (m: Nat ** n = S (double m))
Q9 (S Z) OneOdd = (Z ** Refl)
Q9 (S (S k)) (SSOdd k x) = case (Q9 k x) of
                                (m ** y) => ((S m) ** (apNat (\n: Nat => (S (S n))) k (S(double m)) y))
