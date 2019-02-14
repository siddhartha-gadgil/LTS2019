module Divisors

import ZZ
%access public export
%default total
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


|||If d divides a and b it divides a linear combination of a and b
LinCombDiv:(m:ZZ)->(n:ZZ)->(isDivisible a d)->(isDivisible b d)->(isDivisible ((a*m)+(b*n)) d)
LinCombDiv m n dDiva dDivb = PlusDiv (MultDiv  dDiva m) (MultDiv  dDivb n)


EuclidConservesDivisor:(m:ZZ)->(isDivisible a d)->(isDivisible b d)->(isDivisible (a+(b*(-m))) d)
EuclidConservesDivisor m dDiva dDivb = PlusDiv dDiva (MultDiv dDivb (-m) )

|||Any integer divides zero
ZZDividesZero:(a:ZZ)->(isDivisible 0 a )
ZZDividesZero a = (0**(sym (multZeroRightZeroZ a)))
|||A type that is occupied iff c is a common factor of a and b
isCommonFactorZ : (a:ZZ) -> (b:ZZ) -> (c:ZZ) -> Type
isCommonFactorZ a b c = ((isDivisible a c),(isDivisible b c))
|||The GCD type that is occupied iff d = gcd (a,b). Here GCD is defined as that positive integer such that any common factor of a and b divides it
GCDZ : (a:ZZ) -> (b:ZZ) -> (d:ZZ) -> Type
GCDZ a b d = ((IsPositive d),(isCommonFactorZ a b d),({c:ZZ}->(isCommonFactorZ a b c)->(isDivisible d c)))
|||Anything divides itself
SelfDivide:(a:ZZ)->(isDivisible a a)
SelfDivide a = (1**sym (multOneRightNeutralZ a))

|||Generates the proof that if c is a common factor of a and 0 then c divides a
GCDCondition : (a:ZZ) -> ({c:ZZ}->(isCommonFactorZ a 0 c)->(isDivisible a c))
GCDCondition  a {c} (cDiva,cDiv0) = cDiva
|||Proves that the GCD of a and 0 is a
gcdOfZeroAndInteger:(a:ZZ)->IsPositive a ->GCDZ a 0 a
gcdOfZeroAndInteger a pf = (pf,((SelfDivide a),(ZZDividesZero a)),((GCDCondition a)))
|||The theorem, d|a =>d|(-a)
dDividesNegative:(isDivisible a d)->(isDivisible  (-a) d)
dDividesNegative{a}{d} (x ** pf) = ((-x)**(multNegateRightIsNegateZ a d x pf))
|||The theorem c|b and c|(a+bp) then c|a
cDiva :{p:ZZ} ->(cDIvb :(isDivisible b c))->(cDIvExp:isDivisible (a+(b*p)) c)->(isDivisible a c)
cDiva {p}{b}{a}{c} cDivb cDivExp = rewrite (sym (addAndSubNeutralZ a (b*p))) in (PlusDiv cDivExp (dDividesNegative(MultDiv cDivb (p))))
|||A helper function for euclidConservesGcd function
genFunctionForGcd :(f:({c:ZZ}->(isCommonFactorZ a b c)->(isDivisible d c)))->(({c:ZZ}->(isCommonFactorZ b (a+(b*(-m)))  c)->(isDivisible d c)))
genFunctionForGcd f (cDivb,cDivExp) = f((cDiva cDivb cDivExp,cDivb))

|||The theorem, gcd(a,b)=d => gcd (b, a+ b(-m))=d
euclidConservesGcd :(m:ZZ)->(GCDZ a b d)->(GCDZ b  (a+(b*(-m))) d)
euclidConservesGcd m  (posProof, (dDiva,dDivb), f) = (posProof,(dDivb,(EuclidConservesDivisor m  dDiva dDivb)),genFunctionForGcd f)
|||The theorem that if c and d are positive d|c => (d is less than or equal to c)
posDivPosImpliesLte:(isDivisible c d)->(IsPositive c)->(IsPositive d)->LTEZ d c
posDivPosImpliesLte {d}{c}(x ** pf) cPos dPos = posLteMultPosPosEqZ {q=x} d c dPos cPos pf


|||The Theorem that if c and d are positive, d|c and c|d =>(c=d)
PosDivAndDivByImpliesEqual: (isDivisible c d)->(isDivisible d c)->(IsPositive c)->(IsPositive d) -> (c=d)
PosDivAndDivByImpliesEqual x y z x1 =lteAndGteImpliesEqualZ dLtec cLted where
  dLtec =posDivPosImpliesLte x z x1
  cLted =posDivPosImpliesLte y x1 z
