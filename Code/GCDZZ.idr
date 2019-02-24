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
GCDCalc (Pos (S j)) (Pos  (S k)) Positive NonNegative =
  case QuotRemZ (Pos (S j)) (Pos  (S k)) NonNegative Positive of
    (quot ** (rem  ** (equality, remLessb,remNonNeg))) =>
       (case GCDCalc (Pos (S k)) rem Positive remNonNeg of
             (x ** pf) => (x**(euclidConservesGcdWithProof equality pf)))

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
        (x ** pf) => (x**((negatingPreservesGcdLeft (negatingPreservesGcdRight pf))))
gcdZZ a (Pos (S k)) RightPositive =
  case gcdZZ (Pos (S k)) a LeftPositive of
    (x ** pf) => (x** (gcdSymZ pf))
gcdZZ a (NegS k) RightNegative =
  case gcdZZ (NegS k) a LeftNegative of
      (x ** pf) => (x** (gcdSymZ pf))
