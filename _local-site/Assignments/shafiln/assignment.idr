module shafiln.odds

import Evens

import Intro

data IsOdd : Nat -> Type where
  OneOdd : IsOdd 1
  SSOdd  : (n:Nat) -> IsOdd n -> IsOdd (S (S (n) ))

ThreeOdd : IsOdd 3
ThreeOdd = SSOdd 1 OneOdd

ZeroNotOdd : IsOdd 0->Void
ZeroNotOdd OneOdd impossible
ZeroNotOdd (SSOdd _ _) impossible


TwoNotOdd : IsOdd 2 ->Void
TwoNotOdd (SSOdd Z OneOdd) impossible
TwoNotOdd (SSOdd Z (SSOdd _ _)) impossible

nOddSnEven : (n:Nat)->IsOdd n ->IsEven (S(n))
nOddSnEven (S(Z)) OneOdd = SSEven Z ZEven
nOddSnEven (S (S k)) (SSOdd k x) = SSEven (S(k)) (nOddSnEven k x)

nEvenSnOdd : (n:Nat)->IsEven n ->IsOdd (S(n))
nEvenSnOdd Z ZEven = OneOdd
nEvenSnOdd (S(S k)) (SSEven k x) = SSOdd (S(k)) (nEvenSnOdd k x)


nEvenOrOdd : (n:Nat)->Either (IsEven n) (IsOdd n)
nEvenOrOdd Z = Left ZEven
nEvenOrOdd (S k) = case (nEvenOrOdd k) of
                        (Left l) => Right (nEvenSnOdd k l)
                        (Right r) => Left (nOddSnEven k r)



nNotEvenAndOdd : (n:Nat)->IsEven n ->IsOdd n->Void
nNotEvenAndOdd Z ZEven OneOdd impossible
nNotEvenAndOdd Z ZEven (SSOdd _ _) impossible
nNotEvenAndOdd (S Z) ZEven _ impossible
nNotEvenAndOdd (S Z) (SSEven _ _) _ impossible
nNotEvenAndOdd (S (S k)) (SSEven k x) (SSOdd k y) = nNotEvenAndOdd k x y



oddPlusOddEven : (n:Nat)->(m:Nat)-> IsOdd n ->IsOdd m ->IsEven (add n m)
oddPlusOddEven (S(Z)) m OneOdd y = nOddSnEven m y
oddPlusOddEven (S(S k)) m (SSOdd k x) y = SSEven (add k m) (oddPlusOddEven k m x y)

apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl

oddIsSdouble : (n:Nat)-> IsOdd n ->(m:Nat ** (n = (S(double m))))
oddIsSdouble (S(Z)) OneOdd = (Z ** Refl)
oddIsSdouble (S (S k)) (SSOdd k x) = case (oddIsSdouble k x) of
                                          (m ** pf) => ((S m) ** (apNat (\l => S(S l)) k (S(double m)) pf))
