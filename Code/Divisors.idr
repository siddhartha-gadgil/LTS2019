module Divisors

import ZZ
%access public export
|||isDivisible a b can be constucted if b divides a
isDivisible : ZZ -> ZZ -> Type
isDivisible a b = (n : ZZ ** a = b * n)


|||1 divides everything
oneDiv : (a : ZZ) -> isDivisible a 1
oneDiv a = (a ** rewrite sym (multOneLeftNeutralZ a) in Refl)

|||Genetes a proof of (a+b) = d*(n+m) from (a=d*n)and (b=d*m)
DistributeProof: (a:ZZ)->(b:ZZ)->(d:ZZ)->(n:ZZ)->(m:ZZ)->(a=d*n)->(b=d*m)->((a+b) = d*(n+m))
DistributeProof a b d n m pf1 pf2 = rewrite  (multDistributesOverPlusRightZ d n m) in(trans (the (a+b=(d*n)+b) (v1)) v2) where
  v1 =plusConstantRightZ a (d*n) b pf1
  v2 =plusConstantLeftZ b (d*m) (d*n) pf2

|||The theorem d|a =>d|ac
MultDiv:(isDivisible a d) ->(c:ZZ)->(isDivisible (a*c) d)
MultDiv {d} (n**Refl) c =((n*c)** (rewrite sym (multAssociativeZ d n c) in (Refl)))

|||The theorem d|a and d|b =>d|(a+b)
PlusDiv : (isDivisible a d)->(isDivisible b d)->(isDivisible (a+b) d)
PlusDiv {d}{a}{b} (n**prf1) (m**prf2) = ((n+m)**(DistributeProof a b d n m prf1 prf2))
|||The theorem b|a and c|b =>c|a
TransDivide : (isDivisible a b)->(isDivisible b c)->(isDivisible a c)
TransDivide {c} (x ** pf1) (y ** pf2) = (y*x ** (rewrite  multAssociativeZ c y x in  (rewrite pf1 in (rewrite pf2 in Refl))))

|||Any integer divides zero
ZZDividesZero:(a:ZZ)->(isDivisible 0 a )
ZZDividesZero a = (0**(sym (multZeroRightZeroZ a)))

|||A type that is occupied iff c is a common factor of a and b
isCommonFactorZ : (a:ZZ) -> (b:ZZ) -> (c:ZZ) -> Type
isCommonFactorZ a b c = ((isDivisible a c),(isDivisible b c))

|||The GCD type that is occupied iff d = gcd (a,b). Here GCD is defined as that positive integer such that any common factor of a and b divides it
GCDZ : (a:ZZ) -> (b:ZZ) -> (d:ZZ) -> Type
GCDZ a b d = ((IsPositive d),(isCommonFactorZ a b d),({c:ZZ}->(isCommonFactorZ a b c)->(isDivisible d c)))
