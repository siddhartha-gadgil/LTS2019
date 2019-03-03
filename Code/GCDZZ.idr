module GCDZZ
import Divisors
import ZZ
import NatUtils
import gcd
import ZZUtils
%access public export

|||Converts the expression (a=r+(q*b)) to its integer equivalent
total
ExpNatToZZ:{a:Nat}->{b:Nat}->(a=r+(q*b))->((Pos a)=Pos(r)+((Pos q)*(Pos b)))
ExpNatToZZ Refl = Refl


|||Given a nonnegative integer a and positive integer b, it returns quotient and remainder
|||with proof of (a = rem + (quot * b) and that 0<=rem<b
total
QuotRemZ:(a:ZZ)->(b:ZZ)->IsNonNegative a -> IsPositive b ->
(quot : ZZ ** (rem : ZZ ** ((a = rem + (quot * b)), LTZ rem b,(IsNonNegative rem))))
QuotRemZ (Pos j) (Pos (S k)) NonNegative Positive =
  case (euclidDivide j (S k) (SIsNotZ {x=(k)})) of
    (q ** (r ** (equality, rlessb))) =>
         ((Pos q)**((Pos r)**((ExpNatToZZ equality),(ltNatToZZ rlessb),NonNegative)))




|||Returns gcd of a and b with proof when a is positive and b is nonnegative
GCDCalc :(a:ZZ)->(b:ZZ)->(IsPositive a)->(IsNonNegative b)->(d**(GCDZ a b d))
GCDCalc a (Pos Z) x NonNegative = (a**(gcdOfZeroAndInteger a x))
GCDCalc (Pos (S j)) (Pos  (S k)) Positive NonNegative = assert_total $
  case QuotRemZ (Pos (S j)) (Pos  (S k)) NonNegative Positive of
    (quot ** (rem  ** (equality, remLessb,remNonNeg))) =>
       (case GCDCalc (Pos (S k)) rem Positive remNonNeg of
             (x ** pf) => (x**(euclidConservesGcdWithProof equality pf)))

|||Returns Bezout coefficients with proof for a Positive integer a and
|||NonNegative integer b with proofs of GCD and equality
bez:(a:ZZ)->(b:ZZ)->(IsPositive a)->(IsNonNegative b) ->
   (d**((GCDZ a b d),(m:ZZ**n:ZZ**(d=(m*a)+(n*b)))))
bez a (Pos Z) x NonNegative = (a**((gcdOfZeroAndInteger a x),(1**0**prf))) where
  prf = rewrite (multOneLeftNeutralZ a) in
     (rewrite  (plusZeroRightNeutralZ a) in Refl)
bez (Pos (S j)) (Pos  (S k)) Positive NonNegative = assert_total $
  case QuotRemZ (Pos (S j)) (Pos  (S k)) NonNegative Positive of
      (quot ** (rem  ** (equality, remLessb,remNonNeg))) =>
         (case bez (Pos (S k)) rem Positive remNonNeg of
            (g**((gcdprf),(m1**n1**lincombproof))) =>
               (g**((euclidConservesGcdWithProof equality gcdprf),
                    ((n1)**(m1+(n1*(-quot)))**
                          (bezoutReplace equality lincombproof)))))


|||Returns gcd of two integers with proof given that not both of them are zero
gcdZZ:(a:ZZ)->(b:ZZ)->(NotBothZeroZ a b)->(d**(GCDZ a b d))
gcdZZ (Pos (S k)) (Pos j) LeftPositive =
  GCDCalc (Pos (S k)) (Pos j) Positive NonNegative
gcdZZ (Pos (S k)) (NegS j) LeftPositive =
  case GCDCalc (Pos (S k)) (-(NegS j)) Positive NonNegative of
                (x ** pf) => (x**(negatingPreservesGcdRight pf))
gcdZZ (NegS k) (Pos j) LeftNegative =
  case GCDCalc (-(NegS k)) (Pos j) Positive NonNegative of
    (x**pf) =>(x**(negatingPreservesGcdLeft pf))
gcdZZ (NegS k) (NegS j) LeftNegative =
  case GCDCalc (-(NegS k)) (-(NegS j)) Positive NonNegative of
        (x ** pf) => (x**((negatingPreservesGcdLeft
           (negatingPreservesGcdRight pf))))
gcdZZ a (Pos (S k)) RightPositive = assert_total $
  case gcdZZ (Pos (S k)) a LeftPositive of
    (x ** pf) => (x** (gcdSymZ pf))
gcdZZ a (NegS k) RightNegative = assert_total $
  case gcdZZ (NegS k) a LeftNegative of
      (x ** pf) => (x** (gcdSymZ pf))


|||Returns Bezout coefficients with proof for two integers a and b such that
|||not both of them are zero with proofs of GCD and equality
bezoutCoeffs:(a:ZZ)->(b:ZZ)->NotBothZeroZ a b->
   (d**((GCDZ a b d),(m:ZZ**n:ZZ**(d=(m*a)+(n*b)))))
bezoutCoeffs (Pos (S k)) (Pos j) LeftPositive =
  bez (Pos (S k)) (Pos j) Positive NonNegative
bezoutCoeffs (Pos (S k)) (NegS j) LeftPositive =
  case bez (Pos (S k)) (-(NegS j)) Positive NonNegative of
    (x **( pf,(m**n**lproof))) =>
       (x**((negatingPreservesGcdRight pf),(m**(-n)**
           (rewrite multNegNegNeutralZ n (Pos(S j)) in lproof))))
bezoutCoeffs (NegS k) (Pos j) LeftNegative =
  case bez (-(NegS k)) (Pos j) Positive NonNegative of
    (x**(pf,(m**n**lproof))) =>(x**((negatingPreservesGcdLeft pf),((-m)**n**
       (rewrite multNegNegNeutralZ m (Pos (S k)) in lproof))))
bezoutCoeffs (NegS k) (NegS j) LeftNegative =
  case bez (-(NegS k)) (-(NegS j)) Positive NonNegative of
        (x**(pf,(m**n**lproof))) => (x**((((negatingPreservesGcdLeft
          (negatingPreservesGcdRight pf)))),((-m)**(-n)**
            (rewrite  multNegNegNeutralZ m (Pos (S k)) in
             rewrite  multNegNegNeutralZ n (Pos(S j)) in
              lproof))))
bezoutCoeffs a (Pos (S k)) RightPositive = assert_total $
  case bezoutCoeffs (Pos (S k)) a LeftPositive of
    (x**(pf,(m**n**lproof))) => (x** ((gcdSymZ pf),(n**m**
       (rewrite plusCommutativeZ (n*a) (m*(Pos (S k))) in lproof))))
bezoutCoeffs a (NegS k) RightNegative = assert_total $
  case bezoutCoeffs (NegS k) a LeftNegative of
      (x**(pf,(m**n**lproof))) => (x** ((gcdSymZ pf),(n**m**
         (rewrite plusCommutativeZ (n*a) (m*(NegS k)) in lproof))))

|||Proof that if d = ja + kb, then md = jma + kmb
multOnLeft:{a:ZZ}->(m:ZZ)->(d=(j*a)+(k*b))->((m*d)=j*(m*a)+k*(m*b))
multOnLeft {a}{b}{j}{k}{d} m prf =
  rewrite multAssociativeZ j m a in
  rewrite multAssociativeZ k m b in
  rewrite multCommutativeZ j m in
  rewrite multCommutativeZ k m in
  rewrite sym $ multAssociativeZ m j a in
  rewrite sym $ multAssociativeZ m k b in
  rewrite sym $ multDistributesOverPlusRightZ m (j*a) (k*b) in
  cong prf


|||A helper function for gcdOfMultiple
genfunctionGcdOfMultiple:{a:ZZ}->{b:ZZ}->{d:ZZ}->{k:ZZ}->{j:ZZ}->(d=j*a+k*b)->
 (m:ZZ)->
  ({c:ZZ}->(IsCommonFactorZ (m*a) (m*b) c) -> (IsDivisibleZ (m*d) c))
genfunctionGcdOfMultiple{a}{b}{d}{k}{j} prf  m  commonpf =
  linCombDivLeftWithProof {a=(m*a)}{b=(m*b)}{d=(m*d)} (multOnLeft m prf) commonpf


|||The theorem that if m>0 and a and b are not both zero, then gcd(ma,mb) = m *gcd (a,b)
gcdOfMultiple:(m:ZZ)-> (IsPositive m)->(GCDZ a b d) ->NotBothZeroZ a b->
  (GCDZ (m*a) (m*b) (m*d) )
gcdOfMultiple{a}{b}{d} m mPos (dPos, (dDiva,dDivb),fd)  notzero=
  case bezoutCoeffs a b notzero of
        (g**(gisgcd,(j**k**linpf))) =>
            ((posMultPosIsPos mPos dPos),((multBothSidesOfDiv m dDiva),
                 (multBothSidesOfDiv m dDivb)),
                     (genfunctionGcdOfMultiple{d=d} (rewrite (gcdIsUnique gisgcd (dPos, (dDiva,dDivb),fd)) in linpf) m ))

