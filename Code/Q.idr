module Q
import ZZ
import GCDZZ
import Divisors
import Monoid

data Q : Type where
  PbySq : (p: ZZ) -> (q: Nat) -> Q

ZQ : Q
ZQ = PbySq (Pos Z) Z

OneQ : Q
OneQ = PbySq (Pos (S Z)) Z

|||data type which has the simplified form of a Rational number
data SimpQ : Type where
  SimplifiedQ : Q -> (GCDZ p (Pos(S q)) 1) -> SimpQ



addQ: Q -> Q -> Q
addQ (PbySq p1 q1) (PbySq p2 q2) =
  let
    num : ZZ = (p1 * (Pos(S q2))) + (p2 * (Pos (S q1)))
    denom: Nat = q1 * q2 + q1 + q2
  in
    PbySq num denom

multQ: Q-> Q -> Q
multQ (PbySq p1 q1) (PbySq p2 q2) = PbySq (p1 * p2) (q1 * q2 + q1 + q2)

ZZtoQ : ZZ  -> Q
ZZtoQ x = PbySq x Z

IntegertoQ : Integer -> Q
IntegertoQ x = ZZtoQ(fromInt x)

implementation Num Q where
  (+) = addQ
  (*) = multQ
  fromInteger = IntegertoQ

|||Proves that addition over Q is commutative
addQIsComm : (x:Q)->(y: Q)-> (x+y=y+x)
addQIsComm (PbySq p1 q1) (PbySq p2 q2) =
  rewrite plusCommutativeZ (p1 * (Pos(S q2))) (p2 * (Pos (S q1))) in
  rewrite multCommutative q1 q2 in
  rewrite plusCommutative (q2*q1 + q1) q2 in
  rewrite plusAssociative q2 (q2 * q1) q1 in
  rewrite plusCommutative q2 (q2 * q1) in
  Refl

|||proves that multiplication over Q is commutative
multQisComm : (x:Q)-> (y: Q) -> (x*y = y*x)
multQisComm (PbySq p1 q1) (PbySq p2 q2) =
  rewrite multCommutativeZ p1 p2 in
  rewrite multCommutative q1 q2 in
  rewrite plusCommutative (q2*q1 + q1) q2 in
  rewrite plusAssociative q2 (q2 * q1) q1 in
  rewrite plusCommutative q2 (q2 * q1) in
  Refl

|||Functions to give the IsIdentity type for Q over *
leftMultId : (r : Q) -> (OneQ * r = r)
leftMultId (PbySq p q) = rewrite multOneLeftNeutralZ p in Refl

RightMultId : (r: Q)-> (r * OneQ = r)
RightMultId r = trans (multQisComm r OneQ) (leftMultId r)

OneIsQMultId : (a: Q) -> (a*OneQ =a, OneQ * a = a)
OneIsQMultId a = (RightMultId a, leftMultId a)

|||functions to give the IsIdentity type for Q over +
leftAddId : (r : Q) ->  (ZQ + r = r)
leftAddId (PbySq p q) =
  rewrite multOneRightNeutralZ p in
  rewrite plusZeroLeftNeutralZ p in
  Refl

rightAddId : (r: Q) -> (r + ZQ = r)
rightAddId r = trans (addQIsComm r ZQ) (leftAddId r)

ZIsQAddId : (a:Q)->((a+ZQ)=a, (ZQ+a)=a)
ZIsQAddId a = (rightAddId a, leftAddId a)


|||Auxillary functions
multZero : (n: Nat) -> mult n Z = Z
multZero Z = Refl
multZero (S k) = multZero k

apNatX : (x: Type) -> (f: Nat -> x) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNatX x f m m Refl = Refl

Aux1 : (n: Nat) -> (q : Nat) -> Nat -> Q
Aux1 n q m = PbySq (Pos (plus m n)) q

Aux2: (n: Nat) -> (q: Nat) -> Nat -> Q
Aux2 n q m = PbySq (plusZ (plusZ (Pos 0) (negNat m)) (NegS n)) q
{-
||| The IdentityExists type for Q over +
QAddIdExists : Type
QAddIdExists = (ZQ ** (ZIsQAddId))
-}
