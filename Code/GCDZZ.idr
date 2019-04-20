module GCDZZ
import Divisors
import ZZ
import NatUtils
import NatOrder
import gcd
import ZZUtils
import BoundedGCD
%default total
%access public export

|||Converts the expression (a=r+(q*b)) to its integer equivalent
total
ExpNatToZZ:{a:Nat}->{b:Nat}->(a=r+(q*b))->((Pos a)=Pos(r)+((Pos q)*(Pos b)))
ExpNatToZZ Refl = Refl


|||Given a nonnegative integer a and positive integer b, it returns quotient and
|||remainder with proof of (a = rem + (quot * b) and that 0<=rem<b
total
QuotRemZ:(a:ZZ)->(b:ZZ)->IsNonNegative a -> IsPositive b ->
(quot : ZZ ** (rem : ZZ ** ((a = rem + (quot * b)), LTZ rem b,(IsNonNegative rem))))
QuotRemZ (Pos j) (Pos (S k)) NonNegative Positive =
  case (eculidDivideAux j (S k) (SIsNotZ {x=(k)})) of
    (q ** (r ** (equality, rlessb))) =>
         ((Pos q)**((Pos r)**((ExpNatToZZ equality),(ltNatToZZ rlessb),NonNegative)))

|||Returns Gcd with proof for a positive integer a and a nonNegative
|||integer  b
GCDCalc :(a:ZZ)->(b:ZZ)->(IsPositive a)->(IsNonNegative b)->(d**(GCDZ a b d))
GCDCalc (Pos (S k)) (Pos j) Positive NonNegative =
  (case isLTE (S j) (S k) of
        (Yes prf) => boundedGCDZ (S k) (S k) j lteRefl prf LeftIsNotZero
        (No contra) =>
           let
             ineq = notLTEimpliesLT (S j) (S k) contra
           in
             boundedGCDZ (S j) (S k) j  (lteSuccLeft ineq) lteRefl LeftIsNotZero)

|||Returns Bezout coefficients with proof for a Positive integer a and
|||NonNegative integer b with proofs of GCD and equality
bez:(a:ZZ)->(b:ZZ)->(IsPositive a)->(IsNonNegative b) ->
   (d**((GCDZ a b d),(m:ZZ**n:ZZ**(d=(m*a)+(n*b)))))
bez (Pos (S k)) (Pos j) Positive NonNegative =
  (case isLTE (S j) (S k) of
        (Yes prf) => boundedGCDbez (S k) (S k) j lteRefl prf LeftIsNotZero
        (No contra) =>
           let
             ineq = notLTEimpliesLT (S j) (S k) contra
           in
             boundedGCDbez (S j) (S k) j  (lteSuccLeft ineq) lteRefl LeftIsNotZero)

|||Returns Gcd with proof for integers a and b such that a is not zero
gcdZZLeftNotZero:(a:ZZ)->(b:ZZ)->(NotZero a)->(d**(GCDZ a b d))
gcdZZLeftNotZero (Pos (S k)) (Pos j) PositiveZ =
  GCDCalc (Pos (S k)) (Pos j) Positive NonNegative
gcdZZLeftNotZero (Pos (S k)) (NegS j) PositiveZ =
  case GCDCalc (Pos (S k)) (-(NegS j)) Positive NonNegative of
                (x ** pf) => (x**(negatingPreservesGcdRight pf))
gcdZZLeftNotZero (NegS k) (Pos j) NegativeZ =
  case GCDCalc (-(NegS k)) (Pos j) Positive NonNegative of
    (x**pf) =>(x**(negatingPreservesGcdLeft pf))
gcdZZLeftNotZero (NegS k) (NegS j) NegativeZ =
  case GCDCalc (-(NegS k)) (-(NegS j)) Positive NonNegative of
        (x ** pf) => (x**((negatingPreservesGcdLeft
           (negatingPreservesGcdRight pf))))

|||Returns gcd of two integers with proof given that not both of them are zero
gcdZZ:(a:ZZ)->(b:ZZ)->(NotBothZeroZ a b)->(d**(GCDZ a b d))
gcdZZ (Pos (S k)) b LeftPositive = gcdZZLeftNotZero (Pos (S k)) b PositiveZ
gcdZZ (NegS k) b LeftNegative = gcdZZLeftNotZero (NegS k) b NegativeZ
gcdZZ a (Pos (S k)) RightPositive =
  (case gcdZZLeftNotZero (Pos (S k)) a PositiveZ of
        (d**gcdpf) => (d**(gcdSymZ gcdpf)))
gcdZZ a (NegS k) RightNegative =
  (case gcdZZLeftNotZero (NegS k) a NegativeZ of
        (d ** gcdpf) => (d** (gcdSymZ gcdpf)))

|||Returns Bezout coefficients with proof for two integers a and b such that
|||a is not zero with proofs of GCD and equality
bezCofLeftNotZero:(a:ZZ)->(b:ZZ)->NotZero a->
   (d**((GCDZ a b d),(m:ZZ**n:ZZ**(d=(m*a)+(n*b)))))
bezCofLeftNotZero (Pos (S k)) (Pos j) PositiveZ =
  bez (Pos (S k)) (Pos j) Positive NonNegative
bezCofLeftNotZero (Pos (S k)) (NegS j) PositiveZ =
  case bez (Pos (S k)) (-(NegS j)) Positive NonNegative of
    (x **( pf,(m**n**lproof))) =>
       (x**((negatingPreservesGcdRight pf),(m**(-n)**
           (rewrite multNegNegNeutralZ n (Pos(S j)) in lproof))))
bezCofLeftNotZero (NegS k) (Pos j) NegativeZ =
  case bez (-(NegS k)) (Pos j) Positive NonNegative of
    (x**(pf,(m**n**lproof))) =>(x**((negatingPreservesGcdLeft pf),((-m)**n**
       (rewrite multNegNegNeutralZ m (Pos (S k)) in lproof))))
bezCofLeftNotZero (NegS k) (NegS j) NegativeZ =
  case bez (-(NegS k)) (-(NegS j)) Positive NonNegative of
        (x**(pf,(m**n**lproof))) => (x**((((negatingPreservesGcdLeft
          (negatingPreservesGcdRight pf)))),((-m)**(-n)**
            (rewrite  multNegNegNeutralZ m (Pos (S k)) in
             rewrite  multNegNegNeutralZ n (Pos(S j)) in
              lproof))))

|||Returns Bezout coefficients with proof for two integers a and b such that
|||not both of them are zero with proofs of GCD and equality
bezoutCoeffs:(a:ZZ)->(b:ZZ)->NotBothZeroZ a b->
   (d**((GCDZ a b d),(m:ZZ**n:ZZ**(d=(m*a)+(n*b)))))
bezoutCoeffs (Pos (S k)) b LeftPositive = bezCofLeftNotZero (Pos (S k)) b PositiveZ
bezoutCoeffs (NegS k) b LeftNegative = bezCofLeftNotZero (NegS k) b NegativeZ
bezoutCoeffs a (Pos (S k)) RightPositive =
  (case bezCofLeftNotZero (Pos (S k)) a PositiveZ  of
        (x**(pf,(m**n**lproof))) => (x** ((gcdSymZ pf),(n**m**
           (rewrite plusCommutativeZ (n*a) (m*(Pos (S k))) in lproof)))))
bezoutCoeffs a (NegS k) RightNegative =
  (case bezCofLeftNotZero (NegS k) a NegativeZ of
        (x**(pf,(m**n**lproof))) => (x** ((gcdSymZ pf),(n**m**
           (rewrite plusCommutativeZ (n*a) (m*(NegS k)) in lproof)))))

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

|||The proof that if c = (2*c)*n, then 1 = (2*n)
|||A helper function for gcdZeroZeroContra
helping1: {c:ZZ}->{n:ZZ}->(IsPositive c)->(c = (2*c)*n) ->(1= (2*n))
helping1{n}{c} cPos prf =
  (multRightCancelZ 1 (2*n) c (posThenNotZero cPos) exp) where
    exp = rewrite multOneLeftNeutralZ c in
          rewrite sym $ multAssociativeZ 2 n c in
          rewrite multCommutativeZ n c in
          rewrite multAssociativeZ 2 c n in
          prf
|||Proof that 2=1 is impossible
twoIsNotOne:Pos (S (S Z))= Pos (S Z)->Void
twoIsNotOne Refl impossible
|||Proof that 2= -1 is impossible
twoIsNotMinusOne: (Pos (S (S Z))= (NegS Z))->Void
twoIsNotMinusOne Refl impossible

|||Proof that 1 = (2*n) is impossible
oneIsTwoTimesIntContra:{n:ZZ}-> (1= (2*n))->Void
oneIsTwoTimesIntContra{n} prf =
  (case productOneThenNumbersOne 2 n (sym prf) of
        (Left (a,b )) => twoIsNotOne a
        (Right (a,b)) => twoIsNotMinusOne a)

|||Proof that if c is positive, 2c|c is impossible
twiceDividesOnceContra:IsPositive c ->(IsDivisibleZ  c (2*c) )->Void
twiceDividesOnceContra cPos (n ** pf) =oneIsTwoTimesIntContra( helping1 cPos pf)
|||GCD of 0 and 0 does not exist
gcdZeroZeroContra:{k:ZZ}->(GCDZ 0 0 k)->Void
gcdZeroZeroContra {k} (kPos,(kDivZ1,kDivZ2),fk) =
 twiceDividesOnceContra kPos (fk {c=(2*k)} (zzDividesZero (2*k),zzDividesZero (2*k)))

|||The actual definition of GCD as the 'greatest' common divisor
GCDZr: (a:ZZ) -> (b:ZZ) -> (d:ZZ) -> Type
GCDZr a b d = ((IsCommonFactorZ a b d),
  ({c:ZZ}->(IsCommonFactorZ a b c)->(LTEZ c d)))

|||GCD of 0 and 0 does not exist even in this definition.
gcdrZeroZeroContra:{k:ZZ}->(GCDZr 0 0 k)->Void
gcdrZeroZeroContra{k} ((kDiv1, kDiv2),fk) =
  succNotLteNumZ k (fk((zzDividesZero (1+k)),(zzDividesZero (1+k))))

|||A helper function function for GCDZImpliesGCDZr
helperGCDZImpliesGCDZr:({k:ZZ}->(IsCommonFactorZ a b k)->(IsDivisibleZ d k))->(IsPositive d)->
   {c:ZZ}->(IsCommonFactorZ a b c)->(LTEZ c d)
helperGCDZImpliesGCDZr {d=(Pos (S k))} f Positive {c = (NegS j)} y = NegLessPositive
helperGCDZImpliesGCDZr {d=(Pos (S k))} f Positive {c = (Pos Z)} y = PositiveLTE (LTEZero)
helperGCDZImpliesGCDZr {d=(Pos (S k))} f Positive {c = (Pos (S j))} y =
  posDivPosImpliesLte (f y) Positive Positive

|||Proof that (GCDZ a b d) implies (GCDZr a b d)
GCDZImpliesGCDZr:(GCDZ a b d)->(GCDZr a b d)
GCDZImpliesGCDZr (dPos,cfab,fd) = (cfab,(helperGCDZImpliesGCDZr fd dPos))

|||Rewrites GCDZr a b e as GCDZr c d e , given a prrof that a=c and b=d
gcdReplace:{a:ZZ}->{b:ZZ}->(a=c)->(b=d)->GCDZr a b e -> GCDZr c d e
gcdReplace prf prf1 x = rewrite (sym prf) in
                        rewrite (sym prf1) in
                        x
|||Rewrites GCDZ a b e as GCDZ c d e , given a prrof that a=c and b=d
gcdzReplace:{a:ZZ}->{b:ZZ}->(a=c)->(b=d)->GCDZ a b e -> GCDZ c d e
gcdzReplace prf prf1 x = rewrite (sym prf) in
                        rewrite (sym prf1) in
                        x
|||GCD is unique even in this definition
gcdrIsUnique:(GCDZr a b c)->(GCDZr a b d)->(c=d)
gcdrIsUnique (comfactc,fc) (comfactd,fd) =
  lteAntiSymmetricZ (fc (comfactd)) (fd (comfactc))

|||Proof that (GCDZr a b d) implies (GCDZ a b d)
GCDZrImpliesGCDZ:{a:ZZ}->{b:ZZ}-> (GCDZr a b d)->(GCDZ a b d)
GCDZrImpliesGCDZ {a}{b}{d} gcdr =
  (case checkNotBothZero a b  of
        Left (aZ,bZ) => void (gcdrZeroZeroContra (gcdReplace aZ bZ gcdr))
        Right notZ =>
           (case bezoutCoeffs a b notZ of
                 (g**(gisgcd,(j**k**linpf))) =>
                    rewrite (gcdrIsUnique gcdr (GCDZImpliesGCDZr gisgcd)) in
                        gisgcd))
|||If d = gcd (a,b) then there exists m and n such that d =ma +nb
gcdIsLinComb:(GCDZ a b d)->(m:ZZ**n:ZZ**(d=(m*a)+(n*b)))
gcdIsLinComb {a}{b} gcd =
  (case checkNotBothZero a b  of
        Left (aZ,bZ) => void (gcdZeroZeroContra (gcdzReplace aZ bZ gcd))
        (Right notZ) =>
          (case bezoutCoeffs a b notZ of
                (g**(gisgcd,(j**k**linpf))) =>
                  (j**k**(rewrite (sym(gcdIsUnique gcd gisgcd)) in linpf))))

|||Theorem that if c|ab and gcd (a,c) =1 , then c|b
caCoprimeThencDivb : (IsDivisibleZ (a*b) c)->(GCDZ a c 1)->
   (IsDivisibleZ b c)
caCoprimeThencDivb cDivab gcd1{a}{b}{c} =
  (case gcdIsLinComb gcd1 of
        (m**n**linpf) =>
        linCombDivLeftWithProof {a=(a*b)} {b=(c*b)} {d=b} {c=c} {m=m} {n=n}
             ( rewrite multAssociativeZ m a b in
               rewrite multAssociativeZ n c b in
               rewrite sym $ multDistributesOverPlusLeftZ (m*a) (n*c) b in
               rewrite multCommutativeZ ((m*a)+(n*c)) b in
               (rewriteLeftTimesOneAsLeft (cong linpf)))
                      (cDivab,(multDiv  (selfDivide c) b)))

|||SmallestPosLinComb a b d is a proof that d is the smallest positive
|||linear combination of a and b
SmallestPosLinComb: (a:ZZ)->(b:ZZ)->(d:ZZ)->Type
SmallestPosLinComb a b d = ((IsPositive d),(m**n**(d=(m*a)+(n*b))),
 ({c:ZZ}->{j:ZZ}->{k:ZZ}->(IsPositive c)-> (c=j*a+k*b)->(LTEZ d c)))
|||The theorem that the smallest positive linear combination is unique
smallestPosLinCombIsUnique :(SmallestPosLinComb a b c)->
    (SmallestPosLinComb a b d)->(c=d)
smallestPosLinCombIsUnique (cPos,(m**n**prfc),fc) (dPos,(u**v**prfd),fd) =
  lteAntiSymmetricZ (fd cPos prfc) (fc dPos prfd)

|||Proof that  j+0=j+(n*0) for any integer n
helping2:{j:ZZ}->(n:ZZ)->j+0=j+(n*0)
helping2 n = rewrite multZeroRightZeroZ n in Refl
|||Proof that any linear combination of 0 and 0 is 0
linCombZeroZeroIsZero: (m:ZZ**n:ZZ**(k=(m*0)+(n*0)))->(k=0)
linCombZeroZeroIsZero (m**n**lprf) =
  rewrite sym $ multZeroRightZeroZ m in
  rewrite sym $ plusZeroRightNeutralZ (m*0) in
  rewrite helping2 {j=(m*0)} n in
   lprf

|||The theorem that smallest positive linear combination of Zero andZero
|||doesnt exist
smallestPosLinCombZeroZeroVoid:{k:ZZ}->(SmallestPosLinComb 0 0 k)->Void
smallestPosLinCombZeroZeroVoid (kPos,(m**n**prfk),fk) =
  zeroNotPos (rewrite sym $(linCombZeroZeroIsZero (m**n**prfk)) in kPos)

|||The theorem that gcd(a,b) is less than or equal to any
|||positive linear combination of a and b
gcdIsSmallerThanLinComb: (GCDZ a b d)->
   ({c:ZZ}->{j:ZZ}->{k:ZZ}->(IsPositive c)-> (c=j*a+k*b)->(LTEZ d c))
gcdIsSmallerThanLinComb (dPos,(dDiva,dDivb),fd) cPos prf =
  posDivPosImpliesLte (linCombDivLeftWithProof prf (dDiva,dDivb)) cPos dPos

|||Theorem that gcd(a,b) is the smallest positive linear combination of
|||a and b
gcdIsSmallestPosLinComb: (GCDZ a b d)->(SmallestPosLinComb a b d)
gcdIsSmallestPosLinComb (dPos,(dDiva,dDivb),fd) =
  (case gcdIsLinComb (dPos,(dDiva,dDivb),fd) of
        (m**n**prf) =>
        (dPos,(m**n**prf),
             (gcdIsSmallerThanLinComb (dPos,(dDiva,dDivb),fd))))

|||Rewrites SmallestPosLinComb a b e to SmallestPosLinComb c d e
|||when given a proof that a=c and b=d
smallestPosLinCombReplace:{a:ZZ}->{b:ZZ}->(a=c)->(b=d)->SmallestPosLinComb a b e ->
    SmallestPosLinComb c d e
smallestPosLinCombReplace prf prf1 x = rewrite (sym prf) in
                                       rewrite (sym prf1) in
                                           x
|||Theorem that the smallest positive linear combination of a and b is
|||the gcd of a and b
smallestPosLinCombIsGcd:(SmallestPosLinComb a b d)->(GCDZ a b d)
smallestPosLinCombIsGcd {a} {b} splc =
  (case checkNotBothZero a b of
        (Left (aZ,bZ)) => void (smallestPosLinCombZeroZeroVoid
             (smallestPosLinCombReplace aZ bZ splc))
        Right notZ =>
        (case bezoutCoeffs a b notZ of
              (g**(gisgcd,(j**k**linpf))) =>
                 rewrite (smallestPosLinCombIsUnique splc (gcdIsSmallestPosLinComb gisgcd)) in
                     gisgcd))
