module Divisors

import ZZ
import ZZUtils
%access public export
%default total
|||IsDivisibleZ a b can be constucted if b divides a
IsDivisibleZ : ZZ -> ZZ -> Type
IsDivisibleZ a b = (n : ZZ ** a = b * n)


|||1 divides everything
oneDiv : (a : ZZ) -> IsDivisibleZ a 1
oneDiv a = (a ** rewrite sym (multOneLeftNeutralZ a) in Refl)

|||Genetes a proof of (a+b) = d*(n+m) from (a=d*n)and (b=d*m)
distributeProof: (a:ZZ)->(b:ZZ)->(d:ZZ)->
  (n:ZZ)->(m:ZZ)->(a=d*n)->(b=d*m)->((a+b) = d*(n+m))
distributeProof a b d n m pf1 pf2 =
  rewrite  (multDistributesOverPlusRightZ d n m) in
    (trans (the (a+b=(d*n)+b) (v1)) v2) where
      v1 =plusConstantRightZ a (d*n) b pf1
      v2 =plusConstantLeftZ b (d*m) (d*n) pf2

|||The theorem d|a =>d|ac
multDiv:(IsDivisibleZ a d) ->(c:ZZ)->(IsDivisibleZ (a*c) d)
multDiv {d} (n**Refl) c =
  ((n*c)** (rewrite sym (multAssociativeZ d n c) in (Refl)))
|||The theorem d|a =>d|ca
multDivLeft:(IsDivisibleZ a d) ->(c:ZZ)->(IsDivisibleZ (c*a) d)
multDivLeft{a} x c = rewrite (multCommutativeZ c a) in (multDiv x c)

|||The theorem that if d|a then md|ma
multBothSidesOfDiv:(m:ZZ)->(IsDivisibleZ a d)->(IsDivisibleZ (m*a) (m*d))
multBothSidesOfDiv{d} m (x ** pf) =
  (x** (rewrite (sym (multAssociativeZ m d x)) in (cong pf)))

||| Theorem that if a = k*d and and c|k then c*d|a
multBothSidesOfDivRightWithProof :(a=k*d)->(IsDivisibleZ k c)->
   (IsDivisibleZ a (c*d))
multBothSidesOfDivRightWithProof {a}{k}{c}{d} prf x =
  rewrite prf in
  rewrite (multCommutativeZ k d) in
  rewrite (multCommutativeZ c d) in
   (multBothSidesOfDiv d x)


|||The theorem d|a and d|b =>d|(a+b)
plusDiv : (IsDivisibleZ a d)->(IsDivisibleZ b d)->(IsDivisibleZ (a+b) d)
plusDiv {d}{a}{b} (n**prf1) (m**prf2) =
  ((n+m)**(distributeProof a b d n m prf1 prf2))
|||The theorem b|a and c|b =>c|a
transDivide : (IsDivisibleZ a b)->(IsDivisibleZ b c)->(IsDivisibleZ a c)
transDivide {c} (x ** pf1) (y ** pf2) =
  (y*x ** (rewrite  multAssociativeZ c y x in
     (rewrite pf1 in (rewrite pf2 in Refl))))


|||If d divides a and b it divides a linear combination of a and b
linCombDiv:(m:ZZ)->(n:ZZ)->(IsDivisibleZ a d)->(IsDivisibleZ b d)->
   (IsDivisibleZ ((a*m)+(b*n)) d)
linCombDiv m n dDiva dDivb =
  plusDiv (multDiv  dDiva m) (multDiv  dDivb n)

|||The theorem that d|a and d|b implies d |(a+b*(-m)
euclidConservesDivisor:(m:ZZ)->(IsDivisibleZ a d)->(IsDivisibleZ b d)->
  (IsDivisibleZ (a+(b*(-m))) d)
euclidConservesDivisor m dDiva dDivb = plusDiv dDiva (multDiv dDivb (-m) )

|||Any integer divides zero
zzDividesZero:(a:ZZ)->(IsDivisibleZ 0 a )
zzDividesZero a = (0**(sym (multZeroRightZeroZ a)))
|||A type that is occupied iff c is a common factor of a and b
IsCommonFactorZ : (a:ZZ) -> (b:ZZ) -> (c:ZZ) -> Type
IsCommonFactorZ a b c = ((IsDivisibleZ a c),(IsDivisibleZ b c))
|||The theorem that  d is a common factor of a and b implies
|||d is a common factor of b and a
commonfactSym: IsCommonFactorZ a b d ->IsCommonFactorZ b a d
commonfactSym (dDiva, dDivb) = (dDivb,dDiva)
|||The theorem that if (d=(m*a)+(n*b)) and c is a common factor of a and b, then d|c
linCombDivLeftWithProof:{a:ZZ}->{b:ZZ}->{c:ZZ}->{d:ZZ}->{m:ZZ}->{n:ZZ}->(d=(m*a)+(n*b))->
   (IsCommonFactorZ a b c)-> (IsDivisibleZ d c)
linCombDivLeftWithProof {a}{b}{m}{n}{c}{d}prf (cDiva, cDivb) =
  rewrite prf in
  rewrite multCommutativeZ m a in
  rewrite multCommutativeZ n b in
  linCombDiv m n cDiva cDivb

|||The GCD type that is occupied iff d = gcd (a,b).
||| Here GCD is defined as that positive integer such that any common factor
||| of a and b divides it
GCDZ : (a:ZZ) -> (b:ZZ) -> (d:ZZ) -> Type
GCDZ a b d = ((IsPositive d),(IsCommonFactorZ a b d),
  ({c:ZZ}->(IsCommonFactorZ a b c)->(IsDivisibleZ d c)))
|||Anything divides itself
selfDivide:(a:ZZ)->(IsDivisibleZ a a)
selfDivide a = (1**sym (multOneRightNeutralZ a))

|||Generates the proof that if c is a common factor of a and 0 then c divides a
gcdCondition : (a:ZZ) -> ({c:ZZ}->(IsCommonFactorZ a 0 c)->(IsDivisibleZ a c))
gcdCondition  a {c} (cDiva,cDiv0) = cDiva
|||Proves that the GCD of a and 0 is a
gcdOfZeroAndInteger:(a:ZZ)->IsPositive a ->GCDZ a 0 a
gcdOfZeroAndInteger a pf =
  (pf,((selfDivide a),(zzDividesZero a)),((gcdCondition a)))
|||The theorem, d|a =>d|(-a)
dDividesNegative:(IsDivisibleZ a d)->(IsDivisibleZ  (-a) d)
dDividesNegative{a}{d} (x ** pf) =
  ((-x)**(multNegateRightIsNegateZ a d x pf))
|||The theorem that d|(-a) implies d|a
dDividesNegative2:  (IsDivisibleZ (-a) d)->(IsDivisibleZ  a d)
dDividesNegative2 {a}x = rewrite (sym (doubleNegElim a)) in (dDividesNegative x)
|||The theorem that d|a implies (-d)|a
negativeDivides:(IsDivisibleZ a d)->(IsDivisibleZ a (-d))
negativeDivides {a}{d}(x ** pf) =
  ((-x)**(rewrite pf in (sym negateMultNegateNeutralZ)))
|||The theorem that (-d)|a implies d|a
negativeDivides2:(IsDivisibleZ a (-d))->(IsDivisibleZ a d)
negativeDivides2 {a}{d}x = rewrite (sym (doubleNegElim d)) in (negativeDivides x)
|||The theorem that (d|a) implies ((-d)|(-a))
doubleNegativeDivides : (IsDivisibleZ a d)->(IsDivisibleZ (-a) (-d))
doubleNegativeDivides x = negativeDivides (dDividesNegative x)

|||The theorem that -1|a for all integers
minusOneDivides:(a:ZZ)->(IsDivisibleZ a (-1))
minusOneDivides a = negativeDivides (oneDiv _)
|||The theorem that 0 doesnt divide a non zero quantity
zeroDoesntDivideNonZero:{d:ZZ}->(NotZero d)->(IsDivisibleZ d 0)->Void
zeroDoesntDivideNonZero{d = (Pos (S k))} PositiveZ (x** pf)=
  (posIsNotZeroTimesInteger pf)
zeroDoesntDivideNonZero{d = (NegS k)} NegativeZ (x ** pf) =
  (negSIsNotZeroTimesInteger pf)


|||The theorem c|b and c|(a+bp) then c|a
cDiva :{p:ZZ} ->(cDIvb :(IsDivisibleZ b c))->
  (cDIvExp:IsDivisibleZ (a+(b*p)) c)->(IsDivisibleZ a c)
cDiva {p}{b}{a}{c} cDivb cDivExp =
  rewrite (sym (addAndSubNeutralZ a (b*p))) in (
    plusDiv cDivExp (dDividesNegative(multDiv cDivb (p))))
|||A helper function for euclidConservesGcd function
genFunctionForGcd :(f:({c:ZZ}->(IsCommonFactorZ a b c)->(IsDivisibleZ d c)))->
  (({c:ZZ}->(IsCommonFactorZ b (a+(b*(-m)))  c)->(IsDivisibleZ d c)))
genFunctionForGcd f (cDivb,cDivExp) =
  f((cDiva cDivb cDivExp,cDivb))

|||The theorem, gcd(a,b)=d => gcd (b, a+ b(-m))=d
euclidConservesGcd :(m:ZZ)->(GCDZ a b d)->(GCDZ b  (a+(b*(-m))) d)
euclidConservesGcd m  (posProof, (dDiva,dDivb), f) =
  (posProof,(dDivb,(euclidConservesDivisor m  dDiva dDivb)),genFunctionForGcd f)
|||The theorem that if c and d are positive d|c => (d is less than or equal to c)
posDivPosImpliesLte:(IsDivisibleZ c d)->(IsPositive c)->
  (IsPositive d)->LTEZ d c
posDivPosImpliesLte {d}{c}(x ** pf) cPos dPos =
  posLteMultPosPosEqZ {q=x} d c dPos cPos pf

|||The Theorem that if c and d are positive, d|c and c|d =>(c=d)
posDivAndDivByImpliesEqual: (IsDivisibleZ c d)->(IsDivisibleZ d c)->(IsPositive c)
  ->(IsPositive d) -> (c=d)
posDivAndDivByImpliesEqual x y z x1 = lteAntiSymmetricZ dLtec cLted where
  dLtec = posDivPosImpliesLte x z x1
  cLted = posDivPosImpliesLte y x1 z
|||Gcd of a and b is unique
gcdIsUnique: (GCDZ a b d)-> (GCDZ a b c)->(c=d)
gcdIsUnique {a}{b}{c}{d}(dPos, dCommonFactor,fd) (cPos, cCommonFactor,fc) =
  posDivAndDivByImpliesEqual (fc dCommonFactor) (fd cCommonFactor) cPos dPos
|||A helper function for GcdSym
genFunctionForGcdSym:({c:ZZ}->(IsCommonFactorZ a b c)->(IsDivisibleZ d c))->
   ({c:ZZ}->(IsCommonFactorZ b a c)->(IsDivisibleZ d c))
genFunctionForGcdSym f x = f (commonfactSym x)

|||A helper function for negatingPreservesGcdLeft
genFunctionForGcdNeg:({c:ZZ}->(IsCommonFactorZ (-a) b c)->(IsDivisibleZ d c))->
   ({c:ZZ}->(IsCommonFactorZ a b c)->(IsDivisibleZ d c))
genFunctionForGcdNeg f (cDiva,cDivb) = f (cDivNega,cDivb) where
  cDivNega = (dDividesNegative cDiva)
|||Proof that gcd (a,b)=gcd(b,a)
gcdSymZ: (GCDZ a b d)->(GCDZ b a d)
gcdSymZ (dPos,(dDiva,dDivb),fd) = (dPos, (dDivb, dDiva), (genFunctionForGcdSym fd))


|||Theorem that gcd(-a,b)=gcd(a,b)
negatingPreservesGcdLeft: (GCDZ (-a) b d)->(GCDZ a b d)
negatingPreservesGcdLeft (dPos,(dDivNega,dDivb),fd) =
    (dPos,(dDiva,dDivb),(genFunctionForGcdNeg fd)) where
      dDiva = dDividesNegative2 dDivNega
|||Theorem that gcd (p, -q) = gcd (p,q)
negatingPreservesGcdRight: (GCDZ p (-q) r)->(GCDZ p q r)
negatingPreservesGcdRight {p}{q} x =
  gcdSymZ{a=q}{b=p} (negatingPreservesGcdLeft (gcdSymZ {a=p}{b=(-q)} x))
|||Theorem that gcd (a,b) = gcd (-a,b)
negatingPreservesGcdLeft1:(GCDZ a b d)->(GCDZ (-a) b d)
negatingPreservesGcdLeft1{a} x =
  negatingPreservesGcdLeft (rewrite doubleNegElim a in x)

|||Theorem that if d|rem , d|b and a = rem+(quot*b) then d|a
euclidConservesDivisorWithProof :{a:ZZ}->{b:ZZ}->{quot:ZZ}->{rem:ZZ}->
  (a=rem+(quot*b))->(IsDivisibleZ rem d)->(IsDivisibleZ b d)->(IsDivisibleZ a d)
euclidConservesDivisorWithProof {a}{b}{quot}{rem}equality dDivrem dDivb =
  rewrite equality in (plusDiv dDivrem (multDivLeft dDivb quot))

|||Theorem that a = rem +quot*b implies rem = a + (-quot)*b
auxEqProof:{a:ZZ}->{b:ZZ}->{quot:ZZ}->{rem:ZZ}->(a=rem+(quot *b))->
   (rem = (a + (-quot)*b))
auxEqProof {a}{b}{quot}{rem}prf =
  (rewrite (multNegateLeftZ quot b) in (sym (subOnBothSides a rem (quot*b) prf)))

|||A helper function for euclidConservesGcdWithProof
genfunction:(a=rem+(quot*b))->  ({c:ZZ}->(IsCommonFactorZ b rem c)->(IsDivisibleZ d c))->
     ({c:ZZ}->(IsCommonFactorZ a b c)->(IsDivisibleZ d c))
genfunction prf f (dDiva,dDivb) = f(dDivb,dDivrem) where
  dDivrem = euclidConservesDivisorWithProof (auxEqProof prf) dDiva dDivb

|||Proof that if a=rem +quot*b and gcd (b,rem)=d, then gcd(a,b)=d
euclidConservesGcdWithProof: {a:ZZ}->{b:ZZ}->{quot:ZZ}->{rem:ZZ}->
  (a=rem+(quot*b))->(GCDZ b rem d)->(GCDZ a b d)
euclidConservesGcdWithProof {a}{b}{quot}{rem}equality (dPos,(dDivb,dDivrem),fd) =
  (dPos,(dDiva,dDivb),(genfunction equality fd)) where
     dDiva = euclidConservesDivisorWithProof equality dDivrem dDivb

|||The theorem that if d is positive and cd|d then c=1 or c=-1
cdDividesdThenAbscOne:(IsPositive d)->(IsDivisibleZ d (c*d))->Either (c=1) (c=(-1))
cdDividesdThenAbscOne {c = c}{d = d}x (n ** pf) =
  (case productOneThenNumbersOne c n cnIs1 of
      (Left (a, b)) => Left a
      (Right (a, b)) => Right a) where
        cnIs1 = multRightCancelZ (c*n) 1 d (posThenNotZero x) expression where
          expression = rewrite ( sym (multCommuAndAssocZ1{c=c}{d=d}{n=n})) in
                        rewriteRightAsOneTimesRight{b=d} (sym pf)

|||A helper function for divideByGcdThenGcdOne
genFunctionForDivideByGcdThenGcdOne:({k:ZZ}->(IsCommonFactorZ a b k)->
  (IsDivisibleZ d k))->IsPositive d
   ->(aByd:ZZ)->(bByd:ZZ)->a=aByd*d->b=bByd*d->
         ({c:ZZ}->(IsCommonFactorZ aByd bByd c)->(IsDivisibleZ 1 c))
genFunctionForDivideByGcdThenGcdOne f dPos aByd bByd prf prf1 (cDivaByd,cDivbByd) =
  let cdDivd = f ((multBothSidesOfDivRightWithProof prf cDivaByd),
      (multBothSidesOfDivRightWithProof prf1 cDivbByd))in
  (case (cdDividesdThenAbscOne dPos cdDivd) of
        Left Refl => oneDiv 1
        Right Refl =>minusOneDivides 1)

|||Theorem that gcd ( (a/gcd(a,b)),(b/gcd(a,b)) ) =1
|||Here, (fst (fst (fst (snd dGcdab))))  = (a/gcd(a,b)) by definition of the
|||GCDZ type and similarly (fst (snd (fst (snd dGcdab)))) =(b/gcd(a,b))
divideByGcdThenGcdOne:(dGcdab:(GCDZ a b d))->
  (GCDZ (fst (fst (fst (snd dGcdab))))  (fst (snd (fst (snd dGcdab)))) 1)
divideByGcdThenGcdOne{a}{b}{d} (dPos, ((aByd**amd),(bByd**bmd)),fd) =
  (Positive,((oneDiv _),(oneDiv _)),(genFunctionForDivideByGcdThenGcdOne fd
    dPos aByd bByd eqa eqb)) where
      eqa = rewrite (multCommutativeZ aByd d) in amd
      eqb = rewrite (multCommutativeZ bByd d) in bmd

|||Proves that if c divides one then either c =1 or c=-1
intDividesOneThenIntOne: (IsDivisibleZ 1 c) -> Either (c=1 ) (c = (-1))
intDividesOneThenIntOne (x ** pf) =
   case productOneThenNumbersOne c x (sym pf) of
    (Left (k,j)) => Left k
    (Right (k,j)) => Right k
|||A helper function for gcdOfOneAndInteger
genfunctiongcdOfOneAndInteger:({c:ZZ}->(IsCommonFactorZ a 1 c)->(IsDivisibleZ 1 c))
genfunctiongcdOfOneAndInteger (cDiva,cDiv1) =
  (case intDividesOneThenIntOne cDiv1 of
        (Left cIs1) => rewrite cIs1 in (oneDiv 1)
        (Right cisn1) => rewrite cisn1 in (minusOneDivides 1))
|||Proves that for any integer a , (gcd(a,1))=1
gcdOfOneAndInteger: (a:ZZ)->(GCDZ a 1 1)
gcdOfOneAndInteger a = (Positive, ((oneDiv a),(oneDiv 1)), genfunctiongcdOfOneAndInteger)
