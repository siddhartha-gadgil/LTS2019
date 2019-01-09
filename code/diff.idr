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

ess: (n: Nat) -> (m: Nat) -> (n = m) -> (S (S n)) = (S (S m))
ess m m Refl = Refl

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
threeOdd (PlusTwo (S Z) ZeroEven) impossible
threeOdd (PlusTwo (S Z) (PlusTwo _ _)) impossible

thmEven : (n: Nat) -> Either (IsEven n) (IsEven (S n))
thmEven Z = Left ZeroEven
thmEven (S k) = case thmEven k of
                     (Left l) => Right (PlusTwo k l)
                     (Right r) => Left r

divTwo: (n: Nat) -> IsEven n -> Nat
divTwo Z ZeroEven = 0
divTwo (S (S k)) (PlusTwo k x) = S (divTwo k x)

notSS : (n: Nat) -> IsEven n -> IsEven (S n) -> Void
notSS Z ZeroEven ZeroEven impossible
notSS Z ZeroEven (PlusTwo _ _) impossible
notSS (S (S k)) (PlusTwo k x) (PlusTwo (S k) y) = notSS k x y

double: Nat -> Nat
double Z = Z
double (S k) = S (S (double k))

apNat: (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl

byTwo : (n: Nat) -> IsEven n -> (k: Nat ** (double k) = n)
byTwo Z ZeroEven = (0 ** Refl)
byTwo (S (S k)) (PlusTwo k x) = case byTwo k x of
                                     (a ** pf) => ((S a) ** (apNat (\n => S (S n)) (double a) k pf))
