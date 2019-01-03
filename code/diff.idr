module Diff

sub: (n: Nat) -> (m: Nat) -> (LTE m n) -> Nat
sub n Z LTEZero = n
sub (S right) (S left) (LTESucc x) = sub right left x

rl: (n: Nat) -> LTE n n
rl Z = LTEZero
rl (S k) = LTESucc (rl k)

rs: (n: Nat) -> LTE n (S n)
rs Z = LTEZero
rs (S k) = LTESucc (rs k)

zm : (n: Nat) -> LTE n 0 -> n = 0
zm Z LTEZero = ?zm_rhs_1

es: (n: Nat) -> (m: Nat) -> (n = m) -> S n = S m
es m m Refl = Refl

ans : (n: Nat) -> (m: Nat) -> (LTE n m) -> (LTE m n) -> n = m
ans Z Z LTEZero LTEZero = Refl
ans (S a) (S b) (LTESucc x) (LTESucc y) = es a b (ans a b x y)

contra: (1 = 2) -> Void
contra Refl impossible

data IsEven : Nat -> Type where
  ZeroEven : IsEven 0
  PlusTwo : (n: Nat) -> IsEven n -> IsEven (S (S n))

twoEven : IsEven 2
twoEven = PlusTwo 0 ZeroEven

oneOdd : (IsEven 1) -> Void
oneOdd ZeroEven impossible
oneOdd (PlusTwo _ _) impossible

one: Nat
one = 1

threeOdd : (IsEven 3) -> Void
threeOdd (PlusTwo (S Z) x) = ?threeOdd_rhs_1
