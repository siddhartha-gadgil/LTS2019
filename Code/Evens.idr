module Evens

public export
data IsEven : Nat -> Type where
  ZEven : IsEven 0
  SSEven : (n: Nat) -> IsEven n -> IsEven (S (S n))

twoEven : IsEven 2
twoEven = SSEven 0 ZEven

fourEven : IsEven 4
fourEven = SSEven 2 twoEven

half : (n: Nat) -> IsEven n -> Nat
half Z ZEven = 0
half (S (S k)) (SSEven k x) = S (half k x)
