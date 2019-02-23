module GCDZZ
import Divisors
import ZZ
import NatUtils
import gcd
import ZZUtils


total
ExpNatToZZ:{a:Nat}->{b:Nat}->(a=r+(q*b))->((Pos a)=Pos(r)+((Pos q)*(Pos b)))
ExpNatToZZ Refl = Refl


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
