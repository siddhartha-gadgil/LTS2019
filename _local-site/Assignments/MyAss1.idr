module Gadgil.Ass1

import Evens

-- name your module as above

data IsOdd : Nat -> Type where
  OneOdd : IsOdd 1
  SSOdd : (n: Nat) -> IsOdd n -> IsOdd (S (S n))

notOddZ : IsOdd Z -> Void
notOddZ OneOdd impossible
notOddZ (SSOdd _ _) impossible

notOdd2: IsOdd 2 -> Void
notOdd2 (SSOdd Z OneOdd) impossible
notOdd2 (SSOdd Z (SSOdd _ _)) impossible

evenS : (n: Nat) -> IsEven n -> IsOdd (S n)
evenS Z ZEven = OneOdd
evenS (S (S k)) (SSEven k x) = SSOdd (S k) (evenS k x)
