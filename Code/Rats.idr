module Rats

import ZZ
import ZZUtils
import Rationals

data Rats : Type where
  Rat : (p : ZZ) -> (q: ZZ) -> (pf: NotZero q) -> Rats

numerator: Rats-> ZZ
numerator (Rat p q pf) = p

denominator : Rats -> ZZ
denominator(Rat p q pf) = q

addRats : Rats -> Rats -> Rats
addRats (Rat p q x) (Rat y z w) =
  let
    num = (p * z) + (q * y)
    den = q * z
    pf : NotZero den = productNonZero x w
  in
    Rat num den pf

multRats : Rats -> Rats-> Rats
multRats (Rat p q x) (Rat y z w) =
  let
    num = p * y
    den = q * z
    pf : NotZero den = productNonZero x w
  in
    Rat num den pf


ZZtoRats : ZZ -> Rats
ZZtoRats x = Rat x (Pos(S Z)) PositiveZ

InttoRats : Integer -> Rats
InttoRats x = ZZtoRats (fromInt x)

implementation Num Rats where
  (+) = addRats
  (*) = multRats
  fromInteger = InttoRats

EqualRats : Rats -> Rats-> Type
EqualRats (Rat p q r) (Rat x y z) = (p*y = x*q)

rewriteNonZero : (k : ZZ) -> NotZero k -> NotZero (k*1) = NotZero k
rewriteNonZero k pf = rewrite ( multOneRightNeutralZ k) in Refl
{-
NonZeroIdentity: {a:ZZ}->{x: NotZero (Pos(S Z))}-> (r: NotZero a)-> ((productNonZero r x) = r)
NonZeroIdentity {a=Pos (S q)} {x=(PositiveZ{k=Z})} (PositiveZ{k=q}) =
  rewrite blah Pos(S q)  in Refl
NonZeroIdentity {a= NegS q} {x=(PositiveZ{k=Z})} (NegativeZ{k=q}) = rewrite multOneRightNeutralZ (NegS q) in Refl

ZIsIdentity:(a: Rats) -> ((a + (Rat 0 1 x)) = a )
ZIsIdentity (Rat p (Pos(S k)) PositiveZ) =
  rewrite multOneRightNeutralZ p in
  rewrite multZeroRightZeroZ (Pos(S k)) in
  rewrite plusZeroRightNeutralZ p in
  rewrite multOneRightNeutralZ (Pos(S k)) in
  Refl
ZIsIdentity (Rat p (NegS k) NegativeZ) =
  rewrite multOneRightNeutralZ p in
  rewrite multZeroRightZeroZ (NegS k) in
  rewrite plusZeroRightNeutralZ p in
  rewrite multOneRightNeutralZ (NegS k) in
  Refl

--PostulateEquality : EqualRats x y -> (x=y)
  -}
