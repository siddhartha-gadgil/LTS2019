module TwoVarDiophEq
import ZZ
import ZZUtils
import Divisors
import GCDZZ
import decDivZ
%access public export
%default total

|||Proves that if d = gcd (a,b) and c= xa +yb , then d|c
gcdDivLinComb:GCDZ a b d->c=x*a+y*b -> IsDivisibleZ c d
gcdDivLinComb (dPos,dcommonfactab,fd) prf =
  linCombDivLeftWithProof prf dcommonfactab

|||Proves that if d = gcd (a,b) and d|c, then there exists integers x and y
|||such that c = xa +yb
multipleOfGcdLinComb:GCDZ a b d -> IsDivisibleZ c d ->
    (x:ZZ**y:ZZ** (c = x*a + y*b))
multipleOfGcdLinComb{a} {d}{b} gcdpf (n**eqpf) =
  (case checkNotBothZero a b of
        (Left (aZ, bZ)) => void (gcdZeroZeroContra (gcdzReplace aZ bZ gcdpf))
        (Right r) =>
          (case gcdIsLinComb gcdpf of
                (j**l**gcdlc) => ((n*j)**(n*l)**
                    (rewrite sym $multAssociativeZ n j a in
                     rewrite sym $multAssociativeZ n l b in
                     rewrite sym $ multDistributesOverPlusRightZ n (j*a) (l*b) in
                     rewrite eqpf in
                     rewrite multCommutativeZ d n in
                     cong gcdlc) )))

|||Extracts a/gcd(a,b) from the definition of GCDZ
aByd:GCDZ a b d ->ZZ
aByd dGcdab = (fst (fst (fst (snd dGcdab))))
|||Extracts b/gcd(a,b) from the definition of GCDZ
bByd:GCDZ a b d ->ZZ
bByd dGcdab = (fst (snd (fst (snd dGcdab))))

|||Proves that (b/gcd(a,b))*a = (a/gcd(a,b))*b
divByGcdMultByOtherIsSame:(gcdpf:GCDZ a b d) ->(bByd gcdpf)*a =(aByd gcdpf)*b
divByGcdMultByOtherIsSame {a}{b}{d} (dPos, ((abyd**apf),(bbyd**bpf)),fd) =
  multLeftCancelZ d (bbyd*a) (abyd *b) (posThenNotZero dPos)
    (rewrite multAssociativeZ d bbyd a in
     rewrite multAssociativeZ d abyd b in
     rewrite  sym $ bpf in
     rewrite sym $ apf in
     rewrite multCommutativeZ b a in
     Refl)

|||Proves that for any integer k, k*(-b/(gcd(a,b))) and  k*(a/(gcd(a,b)))
|||are solutions of 0 = xa + yb
homoSolution:(gcdpf:GCDZ a b d)->(k:ZZ)->
   (0 = (k*(-(bByd gcdpf)))*a + (k*((aByd gcdpf)))*b)
homoSolution {a}{b}{d} (dPos, ((abyd**apf),(bbyd**bpf)),fd) k =
  rewrite sym $ multAssociativeZ k (-bbyd) a in
  rewrite sym $ multAssociativeZ k (abyd) b in
  rewrite sym $ multDistributesOverPlusRightZ k ((-bbyd)*a) ((abyd)*b) in
  rewrite multNegateLeftZ bbyd a in
  rewrite divByGcdMultByOtherIsSame (dPos, ((abyd**apf),(bbyd**bpf)),fd) in
  rewrite plusNegateInverseRZ (abyd*b) in
  rewrite multZeroRightZeroZ k in
  Refl

|||Proves that if 0 = xa +yb, then (-b/gcd(a,b)))*y = (a/(gcd(a,b)))*x
divHomoEqByGcd:(gcdpf:GCDZ a b d)->(0 = x*a + y*b)->((-(bByd gcdpf))*y = (aByd gcdpf)*x)
divHomoEqByGcd {x}{y}{a}{b}{d}(dPos, ((abyd**apf),(bbyd**bpf)),fd) prf =
  rewrite sym $plusZeroLeftNeutralZ ((-bbyd)*y) in
  rewrite multNegateLeftZ bbyd y in
  subOnBothSides 0 (abyd*x) ((bbyd)*y)
    (multLeftCancelZ d 0 ((abyd*x)+(bbyd*y)) (posThenNotZero dPos)
     (rewrite multZeroRightZeroZ d in
      rewrite multDistributesOverPlusRightZ d (abyd*x) (bbyd*y) in
      rewrite multAssociativeZ d abyd x in
      rewrite multAssociativeZ d bbyd y in
      rewrite sym $ apf in
      rewrite sym $ bpf in
      rewrite multCommutativeZ a x in
      rewrite multCommutativeZ b y in
      prf))

|||Proves that if  0 = xa + yb then there exists an integer k such that
||| y = k* (a/(gcd(a,b)))
homoOnlySolnForY:(gcdpf:GCDZ a b d)->(0 = x*a + y*b) ->
   (k:ZZ**(y = k * (aByd gcdpf)))
homoOnlySolnForY{a}{b}{d}{x}{y} (dPos, ((abyd**apf),(bbyd**bpf)),fd) prf  =
  (case divHomoEqByGcd (dPos, ((abyd**apf),(bbyd**bpf)),fd) prf  of
    eqpf  =>
     (case caCoprimeThencDivb (x**eqpf) (negatingPreservesGcdLeft1
         (gcdSymZ (divideByGcdThenGcdOne (dPos, ((abyd**apf),(bbyd**bpf)),fd)))) of
           (quot**divpf) => (quot** (rewrite multCommutativeZ quot abyd in divpf))))

|||Proves that if a is not zero then a/(gcd(a,b)) is not zero
divByGcdNotZero:(gcdpf:(GCDZ a b d))->NotZero a ->NotZero (aByd gcdpf)
divByGcdNotZero {a = (Pos (S k))}{b = b}{d = d} (dPos, ((abyd**apf),(bbyd**bpf)),fd)
    PositiveZ = posThenNotZero (posDivByPosIsPos{c=(Pos (S k))} Positive dPos apf)
divByGcdNotZero {a = (NegS k)}{b = b}{d = d} (dPos, ((abyd**apf),(bbyd**bpf)),fd)
NegativeZ = NegSThenNotZero (negDivByPosIsNeg Negative dPos apf)

|||Proves that if a is not zero and 0 =xa + yb, then there exists an integer k such that
||| x= k* there exists an integer k such that
||| y = k* (-b/(gcd(a,b))) and y = k* (a/(gcd(a,b)))
homoOnlySoln:(gcdpf:GCDZ a b d)->(0 = x*a + y*b) ->NotZero a->
   (k:ZZ**((x = k * (-(bByd gcdpf))),(y = k * (aByd gcdpf))))
homoOnlySoln {a}{b}{d}{x}{y} (dPos, ((abyd**apf),(bbyd**bpf)),fd) prf anotz =
   (case divHomoEqByGcd (dPos, ((abyd**apf),(bbyd**bpf)),fd) prf of
        divgpf =>
          (case homoOnlySolnForY (dPos, ((abyd**apf),(bbyd**bpf)),fd) prf of
            (k**adivy) => (k**((multLeftCancelZ abyd x (k*(-bbyd))
              (divByGcdNotZero (dPos, ((abyd**apf),(bbyd**bpf)),fd) anotz)
                (rewrite multAssociativeZ abyd k (-bbyd) in
                 rewrite multCommutativeZ abyd k in
                 rewrite sym $ adivy in
                 rewrite multCommutativeZ y (-bbyd) in
                 sym $ divgpf)),adivy))))
