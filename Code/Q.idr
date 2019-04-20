module Q
import ZZ
import GCDZZ
import Divisors
import Monoid
import Rationals
import ZZUtils
import TwoVarDiophEq
import NatUtils



|||data type for rationals
data Q : Type where
  PbySq : (p: ZZ) -> (q: Nat) -> Q

ZQ : Q
ZQ = PbySq (Pos Z) Z

OneQ : Q
OneQ = PbySq (Pos (S Z)) Z

|||data type which has the simplified form of a Rational number, a transversal group
data SimpQ : Type where
 SimplifiedQ : (p:ZZ) -> (q:ZZ) -> .(IsPositive q) -> .(GCDZ p q 1) -> SimpQ


--Auxillary conversions to convert Q into a SimpQ
QtoZZPair : Q -> ZZPair
QtoZZPair (PbySq p q) = (p, Pos(S q))

SimplifyToZZPair : (x:Q)-> (y: ZZPair ** (GCDZ (fst y) (snd y) 1))
SimplifyToZZPair (PbySq p q)= simplifyWithProof (QtoZZPair (PbySq p q)) (PositiveZ{k=q})

ZZPairtoQ : ZZPair -> Q
ZZPairtoQ (p, Pos(S q)) = PbySq p q

--auxillary functions for conversion of data types

blah: {b:ZZ}-> {d:ZZ}-> (IsPositive b) -> (IsPositive d) -> (x: IsDivisibleZ b d) -> (IsPositive (fst x))
blah Positive Positive ((Pos Z) ** pf) =  void (posIsNotPosTimesZero pf)
blah Positive Positive ((NegS l)** pf) = void(PosTimesNegIsNotPos pf)
blah Positive Positive ((Pos (S l))**pf) = Positive

dDivsb: (GCDZ a b d) -> (IsDivisibleZ b d)
dDivsb dgcdab = (snd (fst (snd dgcdab)))
-- aux end

ZZtoSimpQ : (p:ZZ) ->(q:ZZ) -> (pf: IsPositive q) -> (d : ZZ ** GCDZ p q d) -> SimpQ
ZZtoSimpQ p q pf (d**dgcdab) = SimplifiedQ (aByd dgcdab) (fst (dDivsb dgcdab)) (blah pf (fst dgcdab) (dDivsb dgcdab)) (divideByGcdThenGcdOne dgcdab)

|||Simplifies a rational number to its coprime form
QtoSimpQ : Q -> SimpQ
QtoSimpQ (PbySq p q) = ZZtoSimpQ p (Pos(S q)) Positive (gcdZZ p (Pos (S q)) RightPositive)

|||addition over rational number
addQ: Q -> Q -> Q
addQ (PbySq p1 q1) (PbySq p2 q2) =
  let
    num : ZZ = (p1 * (Pos(S q2))) + (p2 * (Pos (S q1)))
    denom: Nat = q1 * q2 + q1 + q2
  in
  PbySq num denom

|||addition over the transversal group
addSimpQ : SimpQ -> SimpQ -> SimpQ
addSimpQ (SimplifiedQ p1 (Pos(S q1)) Positive gcd1) (SimplifiedQ p2 (Pos(S q2)) Positive gcd2) =
                                          QtoSimpQ (addQ (PbySq p1 q1) (PbySq p2 q2))

||| multiplication over Rationals
multQ: Q-> Q -> Q
multQ (PbySq p1 q1) (PbySq p2 q2) = PbySq (p1 * p2) (q1 * q2 + q1 + q2)

|||Multiplication over the transversal group
multSimpQ : SimpQ -> SimpQ -> SimpQ
multSimpQ (SimplifiedQ p1 (Pos(S q1)) Positive gcd1) (SimplifiedQ p2 (Pos(S q2)) Positive gcd2) =
                                          QtoSimpQ (multQ (PbySq p1 q1) (PbySq p2 q2))


--Conversions from integers to aforementioned types
ZZtoQ : ZZ  -> Q
ZZtoQ x = PbySq x Z

IntegertoQ : Integer -> Q
IntegertoQ x = ZZtoQ(fromInt x)

IntegertoSimpQ : Integer -> SimpQ
IntegertoSimpQ x = QtoSimpQ (IntegertoQ x)

--defining the + and * signs for Q and SimpQ
implementation Num Q where
  (+) = addQ
  (*) = multQ
  fromInteger = IntegertoQ

implementation Num SimpQ where
  (+) = addSimpQ
  (*) = multSimpQ
  fromInteger = IntegertoSimpQ

|||Proves that addition over Q is commutative
addQIsComm : (x:Q)->(y: Q)-> (x+y=y+x)
addQIsComm (PbySq p1 q1) (PbySq p2 q2) =
  rewrite plusCommutativeZ (p1 * (Pos(S q2))) (p2 * (Pos (S q1))) in
  rewrite multCommutative q1 q2 in
  rewrite plusCommutative (q2*q1 + q1) q2 in
  rewrite plusAssociative q2 (q2 * q1) q1 in
  rewrite plusCommutative q2 (q2 * q1) in
  Refl
--auxillary function
apYX : (x: Type)->(y: Type) -> (f: y -> x) -> (n: y) -> (m: y) -> n = m -> f n = f m
apYX x y f m m Refl = Refl

{-
addSimpQisComm : (x: SimpQ) -> (y: SimpQ) ->(x+y = y+x)
addSimpQisComm (SimplifiedQ p1 (Pos(S q1)) Positive gcd1) (SimplifiedQ p2 (Pos(S q2)) Positive gcd2) =
  let
  sum :Q = ( (PbySq p1 q1)+(PbySq p2 q2))
  in
  rewrite addQIsComm (PbySq p1 q1) (PbySq p2 q2) in
  Refl
-}

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



Aux1 : (n: Nat) -> (q : Nat) -> Nat -> Q
Aux1 n q m = PbySq (Pos (plus m n)) q

Aux2: (n: Nat) -> (q: Nat) -> Nat -> Q
Aux2 n q m = PbySq (plusZ (plusZ (Pos 0) (negNat m)) (NegS n)) q
{-
||| The IdentityExists type for Q over +
QAddIdExists : Type
QAddIdExists = (ZQ ** (ZIsQAddId))
-}
