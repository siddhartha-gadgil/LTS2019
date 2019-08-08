module LectureEvens

% access public export

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

double: Nat -> Nat
double Z = Z
double (S k) = S (S (double k))

doubleEven : (n: Nat) -> IsEven (double n)
doubleEven Z = ZEven
doubleEven (S k) = SSEven (double k) (doubleEven k)

halfDouble: Nat -> Nat
halfDouble n = half (double n) (doubleEven n)

oneOdd: IsEven 1 -> Void
oneOdd ZEven impossible
oneOdd (SSEven _ _) impossible

threeOdd : IsEven 3 -> Void
threeOdd (SSEven (S Z) ZEven) impossible
threeOdd (SSEven (S Z) (SSEven _ _)) impossible

nOrSnEven: (n: Nat) -> Either (IsEven n) (IsEven (S n))
nOrSnEven Z = Left ZEven
nOrSnEven (S k) = case (nOrSnEven k) of
                       (Left l) => Right (SSEven k l)
                       (Right r) => Left r

halfRoof: Nat -> Nat
halfRoof n = case (nOrSnEven n) of
                  (Left nEven) => half n nEven
                  (Right snEven) => half (S n) snEven

nSnNotBothEven: (n: Nat) -> (IsEven n) -> IsEven (S n) -> Void
nSnNotBothEven Z ZEven ZEven impossible
nSnNotBothEven Z ZEven (SSEven _ _) impossible
nSnNotBothEven (S (S k)) (SSEven k x) (SSEven (S k) y) = nSnNotBothEven k x y

notNandSnEven : (n: Nat) -> (IsEven n , IsEven (S n)) -> Void
notNandSnEven n (a, b) = nSnNotBothEven n a b

apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl


byTwo : (n: Nat) -> IsEven n -> (k: Nat ** double k = n)
byTwo Z ZEven = (0 ** Refl)
byTwo (S (S k)) (SSEven k x) = step where
  step = case (byTwo k x) of
            (m ** pf) => ((S m) ** apNat (\l => S (S l)) (double m) k pf)

oneOddFamily : Nat -> Type
oneOddFamily Z = ()
oneOddFamily (S Z) = Void
oneOddFamily (S (S k)) = ()

oneOddProof : (n : Nat) -> IsEven n -> oneOddFamily n
oneOddProof Z ZEven = ()
oneOddProof (S (S k)) (SSEven k x) = ()

-- Examples

halfRoof3 : Nat
halfRoof3 = halfRoof 3 -- 2 : Nat

-- Equality added

thmAdd : (a: Nat) -> (b: Nat) -> (a = 0) -> (b = 0) -> (a + b = 0)
thmAdd Z Z Refl Refl = Refl


symmEq : (x : Type) -> (a: x) -> (b: x) -> (a = b) -> (b = a)
symmEq x b b Refl = Refl
