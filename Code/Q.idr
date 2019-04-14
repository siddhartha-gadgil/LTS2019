module Q
import ZZ

data Q : Type where
  PbySq : (p: ZZ) -> (q: Nat) -> Q

ZQ : Q
ZQ = PbySq (Pos Z) Z

add: Q -> Q -> Q
add (PbySq p1 q1) (PbySq p2 q2) =
  let
    num : ZZ = (p1 * (Pos q2)) + p1 + (p2 * (Pos q1)) + p2
    denom: Nat = q1 * q2 + q1 + q2
  in
    PbySq num denom

multZero : (n: Nat) -> mult n Z = Z
multZero Z = Refl
multZero (S k) = multZero k

apNatX : (x: Type) -> (f: Nat -> x) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNatX x f m m Refl = Refl

Aux1 : (n: Nat) -> (q : Nat) -> Nat -> Q
Aux1 n q m = PbySq (Pos (plus m n)) q

Aux2: (n: Nat) -> (q: Nat) -> Nat -> Q
Aux2 n q m = PbySq (plusZ (plusZ (Pos 0) (negNat m )) (NegS n)) q

leftId : (r : Q) -> add ZQ r = r
leftId (PbySq (Pos n) q) =
    apNatX Q (Aux1 n q) _ _ (multZero n)
leftId (PbySq (NegS n) q) =
  let
    pf1 = multZero n
    pf = apNatX Q (Aux2 n q) _ _ pf1
  in
    pf
