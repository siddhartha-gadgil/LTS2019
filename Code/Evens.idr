module Evens

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

even: Nat -> Bool
even Z = True
even (S k) = not (even k)

isTrue : Bool -> Type
isTrue True = Unit
isTrue False = Void

evenOdd : (n: Nat) -> isTrue (even n)
evenOdd Z = ()
evenOdd (S k) = case (even k) of
                     False => ?evenOdd_rhs_1
                     True => ?evenOdd_rhs_3
