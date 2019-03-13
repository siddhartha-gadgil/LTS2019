module TwoVarDiophEq
import ZZ
import ZZUtils
import Divisors
import GCDZZ
import decDivZ
%access public export
%default total

|||Any integer is a solution for c=xa+yb when a=b=c=0
zeroLinCombZeroZero:a=0->b=0->c=0->{x:ZZ}->{y:ZZ}->c=x*a+y*b
zeroLinCombZeroZero az bz cz {x} {y} = rewrite az in
                                       rewrite bz in
                                       rewrite cz in
                                       rewrite multZeroRightZeroZ x in
                                       rewrite multZeroRightZeroZ y in
                                       Refl

|||If a=b=0 and c is not zero, it is impossible that c = xa +yb
notZeroNotLinCombZeroZero:a=0->b=0->NotZero c ->
   {x:ZZ}->{y:ZZ}->c=x*a+y*b->Void
notZeroNotLinCombZeroZero aZ bZ cnotz {x}{y} =
  rewrite aZ in
  rewrite bZ in
  rewrite multZeroRightZeroZ x in
  rewrite multZeroRightZeroZ y in
  (notZeroNonZero cnotz)


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

-- The arguments to the function homoOnlySoln need to be explicit because Idris will not
-- infer the correct arguments in the functions below.

|||Proves that if a is not zero and 0 =xa + yb, then there exists an integer k such that
||| x = k* (-b/(gcd(a,b))) and y = k* (a/(gcd(a,b)))
homoOnlySoln:(x: ZZ) -> (y: ZZ) -> (gcdpf:GCDZ a b d)->(0 = x*a + y*b) ->NotZero a->
   (k:ZZ**((x = k * (-(bByd gcdpf))),(y = k * (aByd gcdpf))))
homoOnlySoln {a}{b}{d} x y (dPos, ((abyd**apf),(bbyd**bpf)),fd) prf anotz =
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

|||Given three integers a, b and c, it outputs either
|||a proof that c = xa +yb is impossible or
|||a proof that all integers x and y satisfy the equation (this happens when a=b=c=0)
|||or 4 integers x1 , y1 , pa and pb such that for any integer k,
|||x=x1+k*pa  y=y1+k*pb is a solution of c=xa+yb
|||and whenever c=xa+yb ,there exists an integer, k such that
||| x=x1+k*pa  y=y1+k*pb
findAllSolutions: (a:ZZ)->(b:ZZ)->(c:ZZ)->
  Either ({x:ZZ}->{y:ZZ}->c=x*a+y*b->Void)
  (Either ({x:ZZ}->{y:ZZ}->c=x*a+y*b)
    (x1:ZZ**y1:ZZ**pa:ZZ**pb:ZZ**(({k:ZZ}->(x=x1+k*pa)->(y=y1+k*pb)->(c=x*a+y*b)),
      ((c=x*a+y*b)->(k**((x=x1+k*pa),(y=y1+k*pb)))))))
findAllSolutions a b c =
  (case checkNotBothZero a b of
        (Left (aZ,bZ)) =>
           (case decZero c of
                 (Yes cnotz) => Left (notZeroNotLinCombZeroZero aZ bZ cnotz)
                 (No ciszero) => Right (Left (zeroLinCombZeroZero aZ bZ
                    (notNotZeroThenZero ciszero))))
        (Right abnotZ) =>
          (case gcdZZ a b abnotZ of
            (g**gcdpf) =>
             (case decDivisibleZ c g of
                   (Yes prf) => ?findAllSolutions_rhs_1
                   (No contra) => Left (contra . (gcdDivLinComb gcdpf) ))))

-- The goal of the following section is to show that the non-homogeneous equation is uniquely solved by the family of
-- solutions ((x_p+k*x_0), (y_p+k*y_0)).

||| Produces the difference of two solutions. It will used to show that the difference of two particular
||| solutions satisfies the homogeneous equation.

solDifference: (a: ZZ) -> (b: ZZ) -> (c: ZZ) -> (x1: ZZ) -> (y1: ZZ) -> (x2: ZZ) ->
(y2: ZZ) -> (c=(x1*a+y1*b)) -> (c=(x2*a+y2*b)) -> ( 0= ( ((x1-x2)*a) + ((y1-y2)*b) ))
solDifference a b c x1 y1 x2 y2 prf prf1 = rewrite (multDistributesOverPlusLeftZ (x1) (-x2) (a)) in
                                           rewrite (multDistributesOverPlusLeftZ (y1) (-y2) (b)) in
                                           rewrite sym (plusAssociativeZ (x1*a) ((-x2)*a) (y1*b+((-y2)*b)) ) in
                                           rewrite (plusCommutativeZ (y1*b) ((-y2)*b)) in
                                           rewrite (plusAssociativeZ ((-x2)*a) ((-y2)*b) (y1*b)) in
                                           rewrite (plusCommutativeZ (((-x2)*a) + ((-y2)*b)) (y1*b)) in
                                           rewrite (plusAssociativeZ (x1*a) (y1*b) (((-x2)*a) + ((-y2)*b))) in
                                           rewrite (multNegateLeftZ (x2) (a)) in
                                           rewrite (multNegateLeftZ (y2) (b)) in
                                           rewrite sym (negateDistributesPlus (x2*a) (y2*b)) in
                                           rewrite sym (plusNegateInverseLZ (x2*a+y2*b)) in
                                           rewrite sym prf in
                                           rewrite sym prf1 in
                                           rewrite (plusNegateInverseLZ c) in
                                           Refl

||| Adding x2 to both sides of the equation:
addToSol: (x1: ZZ) -> (x2: ZZ) -> (x1-x2=d) -> (x1=x2+d)
addToSol x1 x2 prf = rewrite sym prf in
                       rewrite (plusCommutativeZ (x1) (-x2)) in
                       rewrite (plusAssociativeZ (x2) (-x2) (x1)) in
                       rewrite (plusNegateInverseLZ (x2)) in
                       rewrite (plusZeroLeftNeutralZ (x1)) in
                       Refl

||| Proves that two particular solutions differ by a solution of the homogeneous equation.
diffIsHomogeneous: {a: ZZ} -> {b: ZZ} -> {c: ZZ} -> {d: ZZ} ->  {x1: ZZ} -> {y1: ZZ} -> {x2: ZZ} ->
{y2: ZZ} -> (IsDivisibleZ c d) -> (gcdpf:GCDZ a b d) -> (NotZero a) -> (NotZero b) -> (c=x1*a+y1*b) -> (c=x2*a+y2*b) -> (k:ZZ** (( (x1-x2) = (k * (-(bByd gcdpf)))),( (y1-y2) = (k * (aByd gcdpf)))))
diffIsHomogeneous {a}{b}{c}{d}{x1}{y1}{x2}{y2} x gcdpf y z prf prf1 = homoOnlySoln {a}{b}{d} (x1-x2) (y1-y2) (gcdpf) (solDifference a b c x1 y1 x2 y2 prf prf1) (y)

||| Proves that any solution is a particular solution plus a constant multiple of the solution of
||| the homogeneous equation.
differByHomogeneous: {a: ZZ} -> {b: ZZ} -> {c: ZZ} -> {d: ZZ} ->  {x1: ZZ} -> {y1: ZZ} -> {x2: ZZ} ->
{y2: ZZ} -> (IsDivisibleZ c d) -> (gcdpf:GCDZ a b d) -> (NotZero a) -> (NotZero b) -> (c=x1*a+y1*b) -> (c=x2*a+y2*b) -> (k:ZZ** (( x1 = x2 + (k * (-(bByd gcdpf)))),( y1 = y2 + (k * (aByd gcdpf)))))
differByHomogeneous x gcdpf y z prf prf1 = ?hole
