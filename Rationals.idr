module Rationals

isFactorInt : Integer -> Integer -> Type  --Needed for defining Integer division
isFactorInt m n = (k : Integer ** (m * k = n))

divides : (m: Integer) -> (n: Integer) -> (k: Integer ** (m * k = n)) -> Integer
divides m n k = (fst k)

Pair : Type
Pair = (Integer, Integer)

Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat) --Euclidean algorithm implemented by Chinmaya
Eucl Z b = (0,0)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False => (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True => (0, S k)

gcdab : Nat -> Nat -> Nat -- Produces the GCD of two numbers. This will be useful to produce the simplified form of a rational number.
gcdab b Z = b
gcdab a b = gcdab b (snd (Eucl a b))

data NotZero : Integer -> Type where --Proof that a number is not zero, needed to construct Q
  OneNotZero : NotZero 1
  NegativeNotZero : ( n: Integer ) -> NotZero n -> NotZero (-n)
  PositiveNotZero : ( m: Integer ) -> LTE 1 (fromIntegerNat m)  -> NotZero m

make_rational : (p: Nat) -> (q: Integer) -> NotZero q -> Pair
make_rational p q x = (toIntegerNat(p), q)

InclusionMap : (n : Nat) -> Pair --Includes the naturals in Q
InclusionMap n = make_rational n 1 OneNotZero

AddRationals : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (snd y) -> Pair
AddRationals x a y b = ((fst x)*(snd y) + (snd x)*(fst y), (snd x)*(snd y))

MultiplyRationals : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (snd y) -> Pair
MultiplyRationals x a y b =((fst x)*(fst y), (snd x)*(snd y))

MultInverse : (x: Pair) -> NotZero (fst x) -> NotZero (snd x) -> Pair
MultInverse x y z = ((snd x), (fst x))

AddInverse : (x: Pair) -> NotZero (snd x) -> Pair
AddInverse x a = (-(fst x), (snd x))

Subtraction : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (snd y) -> Pair
Subtraction x a y b = AddRationals x a (AddInverse y b) b

Division : (x: Pair) -> NotZero (snd x) -> (y: Pair) -> NotZero (fst y) -> NotZero (snd y) -> Pair
Division x a y b c = MultiplyRationals x a (MultInverse y b c) b



--SimplifyRational : (x: Pair) -> NotZero (snd x) -> Pair
--SimplifyRational x a = (divides (gcdab fromIntegerNat((fst x)) fromIntegerNat((snd x))) ___ (fst x), divides (gcdab fromIntegerNat((fst x)) fromIntegerNat((snd x)) __ (snd x))


--Above, I will need to supply a proof that the GCD divides the two numbers. Then, the function defined above will produce the rational in simplified form.
