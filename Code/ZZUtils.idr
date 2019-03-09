module ZZUtils
import ZZ
import NatUtils
%access public export
%default total

data IsNonNegative : ZZ->Type where
 NonNegative :(IsNonNegative (Pos k))


data NotBothZeroZ :ZZ->ZZ->Type where
  LeftPositive :NotBothZeroZ (Pos (S k)) m
  LeftNegative :NotBothZeroZ (NegS k) m
  RightPositive :NotBothZeroZ m (Pos (S k))
  RightNegative :NotBothZeroZ m (NegS k)

data NotZero:ZZ->Type where
  PositiveZ:NotZero (Pos (S k))
  NegativeZ:NotZero (NegS k)

data IsNegative:ZZ->Type where
  Negative: IsNegative (NegS k)

|||Zero is not positive
zeroNotPos:IsPositive (Pos Z)->Void
zeroNotPos Positive impossible

|||Proof that NotBothZeroZ 0 0 is uninhabited
zeroZeroBothZero:NotBothZeroZ (Pos Z) (Pos Z) ->Void
zeroZeroBothZero LeftPositive impossible
zeroZeroBothZero LeftNegative impossible
zeroZeroBothZero RightPositive impossible
zeroZeroBothZero RightNegative impossible

|||Decides whther two numbers are not both zero or not.
decNotBothZero : (a:ZZ)->(b:ZZ)->Dec (NotBothZeroZ a b)
decNotBothZero (Pos Z) (Pos Z) = No ( zeroZeroBothZero)
decNotBothZero (Pos Z) (Pos (S k)) = Yes RightPositive
decNotBothZero (Pos Z) (NegS k) = Yes RightNegative
decNotBothZero (Pos (S k)) b = Yes LeftPositive
decNotBothZero (NegS k) b = Yes LeftNegative

|||Checks 2 numbers and produces a proof of either (a=0,b=0) or (NotBothZeroZ a b)
checkNotBothZero : (a:ZZ)->(b:ZZ)->Either ((a=0),(b=0)) (NotBothZeroZ a b)
checkNotBothZero (Pos Z) (Pos Z) = Left (Refl, Refl)
checkNotBothZero (Pos Z) (Pos (S k)) = Right RightPositive
checkNotBothZero (Pos Z) (NegS k) = Right RightNegative
checkNotBothZero (Pos (S k)) b = Right LeftPositive
checkNotBothZero (NegS k) b = Right LeftNegative

|||Proof that positive numbers are not zero
posThenNotZero:{a:ZZ}->(IsPositive a)->(NotZero a)
posThenNotZero {a = (Pos (S k))} Positive = PositiveZ

NegSThenNotZero:{a:ZZ}->(IsNegative a)->(NotZero a)
NegSThenNotZero {a = (NegS k)} ZZUtils.Negative = NegativeZ

|||Rewrites a=b as a=1*b
rewriteRightAsOneTimesRight: {a:ZZ}->{b:ZZ}->(a=b)->(a=(1*b))
rewriteRightAsOneTimesRight {a}{b}prf = rewrite ( (multOneLeftNeutralZ b)) in prf
|||Rewrites a=b as 1*a=b
rewriteLeftAsOneTimesLeft: {a:ZZ}->{b:ZZ}->(a=b)->(1*a=b)
rewriteLeftAsOneTimesLeft {a}{b}prf = rewrite ( (multOneLeftNeutralZ a)) in prf
|||Rewrites 1*a = b as a=b
rewriteOneTimesLeftAsLeft:{a:ZZ}->{b:ZZ}->((1*a) = b)->(a=b)
rewriteOneTimesLeftAsLeft {a}{b}prf  =
  rewrite ( sym $(multOneLeftNeutralZ a)) in prf
|||Rewrites   (a*1)=b as a=b
rewriteLeftTimesOneAsLeft : {a:ZZ}->{b:ZZ}->((a*1)=b)->(a=b)
rewriteLeftTimesOneAsLeft {a}{b}prf =
  rewrite ( sym $(multOneRightNeutralZ a)) in prf

|||Proof that negative integers are not non negative
negsAreNotNonNegs:(IsNonNegative (NegS k))->Void
negsAreNotNonNegs NonNegative impossible
|||A function that checks whether an integer is non negative and returns a
|||proof or a contradiction
decideIsNonNeg:(a: ZZ) -> Dec (IsNonNegative   a)
decideIsNonNeg (Pos k) = Yes NonNegative
decideIsNonNeg (NegS k) = No (negsAreNotNonNegs)
|||Proof that natural numbers are non negative
naturalsNonNegative: (x:Nat)->IsNonNegative (Pos x)
naturalsNonNegative x = NonNegative

|||The less than type for ZZ
LTZ :ZZ->ZZ->Type
LTZ a b = LTEZ (1+a) b

|||Theorem that if a and b are natural numbers and a<b
|||then, (Pos a) <(Pos b)
ltNatToZZ:{a:Nat}->{b:Nat}->(LT a b)->(LTZ (Pos a) (Pos b))
ltNatToZZ (LTESucc x) = PositiveLTE (LTESucc x)
|||Proves that a<= a for any integer a
lteReflZ:{a:ZZ}->LTEZ a a
lteReflZ {a =(Pos k)} = PositiveLTE (lteRefl {n=k})
lteReflZ {a= (NegS k)} = NegativeLte (lteRefl {n=k})
|||Proof that a number is less than its successor
numLtSucc:(a:ZZ)->LTZ a (1+a)
numLtSucc a = lteReflZ
|||Proof that one is not less than zero
oneNotLTEZero:(LTEZ (Pos (S Z)) (Pos Z))->Void
oneNotLTEZero (PositiveLTE LTEZero) impossible
oneNotLTEZero (PositiveLTE (LTESucc _)) impossible
|||Proof that a number greater than or equal to 1 is positive
gteOnePositive:(a:ZZ)->(LTEZ 1 a)->(IsPositive a)
gteOnePositive (Pos Z) (PositiveLTE LTEZero) impossible
gteOnePositive (Pos Z) (PositiveLTE (LTESucc _)) impossible
gteOnePositive (Pos (S k)) x = Positive
gteOnePositive (NegS _) (PositiveLTE _) impossible
gteOnePositive (NegS _) NegLessPositive impossible
gteOnePositive (NegS _) (NegativeLte _) impossible

|||Proof that it is impossible that (1+a)<=a
succNotLteNumZ:(a:ZZ)->(LTEZ (1+a) a) ->Void
succNotLteNumZ (Pos k)  y =
  impliesContrapositive (LTEZ (Pos (S k)) (Pos k)) (LTE (S k) k)
    LTEZZtoNat  (succNotLTEnum k) y
succNotLteNumZ (NegS Z)  (PositiveLTE _)  impossible
succNotLteNumZ (NegS Z)  NegLessPositive  impossible
succNotLteNumZ (NegS Z)  (NegativeLte _)  impossible
succNotLteNumZ (NegS (S k))  y  =
  impliesContrapositive (LTEZ (NegS k) (NegS (S k))) (LTE (S k) k)
     LTEZZtoNatNeg (succNotLTEnum k) y

|||Multiplying positive numbers gives a positive number.
posMultPosIsPos: (IsPositive m)->(IsPositive d)->(IsPositive (m*d))
posMultPosIsPos{m = (Pos (S k))}{d = (Pos (S j))} Positive Positive = Positive
|||The theorem that (-a)*(-b)=a*b
negateMultNegateNeutralZ: {a:ZZ}->{b:ZZ}->((-a)*(-b)=a*b)
negateMultNegateNeutralZ{a}{b} =
  rewrite (multNegateRightZ (-a) b) in
  rewrite (multNegateLeftZ a b ) in
  rewrite (doubleNegElim (a*b)) in Refl
|||Proof that zero times an integer is not positive
posIsNotZeroTimesInteger:((Pos (S k))=(Pos Z)*a)->Void
posIsNotZeroTimesInteger{a = (Pos _)} Refl impossible
posIsNotZeroTimesInteger{a = (NegS _)} Refl impossible
|||Proof that Zero times an integer is not negative
negSIsNotZeroTimesInteger :((NegS k)=(Pos Z)*a)->Void
negSIsNotZeroTimesInteger {a = (Pos _)} Refl impossible
negSIsNotZeroTimesInteger {a = (NegS _)} Refl impossible
|||Converts a nonNegative integer into the corresponding Natural number
nonNegIntegerToNat:(a:ZZ)->(IsNonNegative a)->Nat
nonNegIntegerToNat (Pos k) NonNegative = k
|||Proof that a positive number is not zero times a negative number
zeroTimesNegIsNotPos:(Pos (S k)) = (Pos Z)*(NegS j)->Void
zeroTimesNegIsNotPos Refl impossible
|||Proof that a positive number is not a negative number times zero
negTimesZeroIsNotPos :(Pos (S k)) = (NegS j)*(Pos Z)->Void
negTimesZeroIsNotPos {k}{j}prf =
  zeroTimesNegIsNotPos{k=k}{j=j}
     (rewrite (sym(multCommutativeZ (NegS j) (Pos Z))) in prf)

|||Lemma that (c*d)*n = (c*n)*d
multCommuAndAssocZ1: {c:ZZ}->{d:ZZ}->{n:ZZ}->(c*d)*n = (c*n)*d
multCommuAndAssocZ1 {c}{d}{n}= rewrite (sym(multAssociativeZ c n d)) in
                           rewrite (multCommutativeZ n d ) in
                           rewrite( (multAssociativeZ c d n))in
                           Refl



|||Proof that if (a*b=1) then either (a=1,b=1)  or (a=-1,b=-1)
productOneThenNumbersOne: (a:ZZ)->(b:ZZ)->(a*b=1) ->Either (a=1,b=1) (a=(-1),b=(-1))
productOneThenNumbersOne (Pos Z) (Pos _) Refl impossible
productOneThenNumbersOne (Pos Z) (NegS _) Refl impossible
productOneThenNumbersOne (Pos (S Z)) (Pos Z) prf = void (posIsNotPosMultZero {k=Z} (sym prf))
productOneThenNumbersOne (Pos (S Z)) (Pos (S Z)) prf = Left (Refl, Refl)
productOneThenNumbersOne (Pos (S Z)) (Pos (S (S _))) Refl impossible
productOneThenNumbersOne (Pos (S Z)) (NegS _) Refl impossible
productOneThenNumbersOne (Pos (S (S k))) (Pos Z) prf = void (posIsNotPosMultZero  (sym prf))
productOneThenNumbersOne (Pos (S (S _))) (Pos (S Z)) Refl impossible
productOneThenNumbersOne (Pos (S (S _))) (Pos (S (S _))) Refl impossible
productOneThenNumbersOne (Pos (S (S _))) (NegS _) Refl impossible
productOneThenNumbersOne (NegS Z) (Pos Z) Refl impossible
productOneThenNumbersOne (NegS Z) (Pos (S _)) Refl impossible
productOneThenNumbersOne (NegS Z) (NegS Z) prf = Right (Refl,Refl)
productOneThenNumbersOne (NegS Z) (NegS (S _)) Refl impossible
productOneThenNumbersOne (NegS (S k)) (Pos Z) prf = void (negTimesZeroIsNotPos{k=Z} (sym prf))
productOneThenNumbersOne (NegS (S _)) (Pos (S _)) Refl impossible
productOneThenNumbersOne (NegS (S _)) (NegS Z) Refl impossible
productOneThenNumbersOne (NegS (S _)) (NegS (S _)) Refl impossible

|||Right cancellation law for multiplication when right is positive
multRightCancelPosZ:(left1:ZZ)->(left2:ZZ)->(right:ZZ)->
   IsPositive right->(left1*right=left2*right)->(left1 = left2)
multRightCancelPosZ (Pos j) (Pos i) (Pos (S k)) Positive prf =
 cong (multRightCancel j i (S k) SIsNotZ expression) where
   expression = posInjective prf
multRightCancelPosZ (Pos _) (NegS _) (Pos (S _)) Positive Refl impossible
multRightCancelPosZ (NegS _) (Pos _) (Pos (S _)) Positive Refl impossible
multRightCancelPosZ (NegS j) (NegS i) (Pos (S k)) Positive prf =
  cong (succInjective j i (multRightCancel (S j) (S i) (S k) SIsNotZ expression)) where
    expression = posInjective (negativesSameNumbersSame prf)


|||Right cancellation law for multiplication given a proof that right is not zero
multRightCancelZ:(left1:ZZ)->(left2:ZZ)->(right:ZZ)->
   NotZero right->(left1*right=left2*right)->(left1 = left2)
multRightCancelZ left1 left2 (Pos (S k)) PositiveZ prf =
  multRightCancelPosZ left1 left2 (Pos (S k)) Positive prf
multRightCancelZ left1 left2 (NegS k) NegativeZ prf =
  multRightCancelPosZ left1 left2 (-(NegS k)) Positive expression where
    expression = rewrite (multNegateRightZ left1 (NegS k)) in
                 rewrite (multNegateRightZ left2 (NegS k)) in
                  (numbersSameNegativesSame prf)
|||Left Cancellation law for multiplication given a proof that left is not zero
multLeftCancelZ :(left : ZZ) -> (right1 : ZZ) -> (right2 : ZZ) ->
  NotZero left -> (left*right1 = left*right2) -> (right1 = right2)
multLeftCancelZ left right1 right2 x prf =
  multRightCancelZ right1 right2 left x expression where
    expression = rewrite (multCommutativeZ right1 left) in
                 rewrite (multCommutativeZ right2 left) in
                  prf

|||Proof that (-a)*(-b) = a*b
multNegNegNeutralZ: (a:ZZ)->(b:ZZ)->(-a)*(-b)=a*b
multNegNegNeutralZ a b =
  rewrite multNegateRightZ (-a) b in
  rewrite multNegateLeftZ a b in
  rewrite doubleNegElim (a*b) in
  Refl

|||The theorem that if  a =r+q*b and g = (m1*b)+(n1*rem)
|||Then g = (n1*a) + ((m1+n1*(-quot))*b)
bezoutReplace:{a:ZZ}->{b:ZZ}->{m1:ZZ}->{rem:ZZ}->
  {quot:ZZ}->{n1:ZZ}->{g:ZZ}-> (a = rem + (quot *b))->
     (g=(m1*b)+(n1*rem))->(g = (n1*a) + ((m1+n1*(-quot))*b))
bezoutReplace {a}{b}{m1}{rem}{quot}{n1}{g}prf prf1 =
  rewrite multDistributesOverPlusLeftZ m1 (n1*(-quot)) b in
  rewrite prf in
  rewrite multDistributesOverPlusRightZ n1 rem (quot*b) in
  rewrite (sym (plusAssociativeZ (n1*rem) (n1*((quot)*b)) ((m1*b)+((n1*(-quot))*b)))) in
  rewrite (plusCommutativeZ (m1*b) ((n1*(-quot))*b)) in
  rewrite (plusAssociativeZ (n1*((quot)*b)) ((n1*(-quot))*b) (m1*b)) in
  rewrite (multAssociativeZ n1 quot b) in
  rewrite (sym (multDistributesOverPlusLeftZ (n1*quot) (n1*(-quot)) b)) in
  rewrite (sym(multDistributesOverPlusRightZ n1 quot (-quot))) in
  rewrite (plusNegateInverseLZ quot) in
  rewrite (multZeroRightZeroZ n1) in
  rewrite (multZeroLeftZeroZ b) in
  rewrite (plusZeroLeftNeutralZ (m1*b)) in
  rewrite (plusCommutativeZ (n1*rem) (m1*b)) in
   prf1


zeroNotNonZero: (NotZero (Pos Z)) -> Void
zeroNotNonZero PositiveZ impossible
zeroNotNonZero NegativeZ impossible

decZero: (a: ZZ) -> Dec (NotZero a)
decZero (Pos Z) = No zeroNotNonZero
decZero (Pos (S k)) = Yes (posThenNotZero Positive)
decZero (NegS k) = Yes (NegSThenNotZero Negative)

nonZeroNotZero: (a: ZZ) -> ( (a = (Pos Z) ) -> Void) -> (NotZero a)
nonZeroNotZero (Pos Z) f = void (f Refl)
nonZeroNotZero (Pos (S k)) f = PositiveZ
nonZeroNotZero (NegS k) f = NegativeZ

ZZSisNotZ: (k: Nat) -> ((Pos (S k))= (Pos Z)) -> Void
ZZSisNotZ _ Refl impossible

ZZNegisNotZ: (k: Nat) -> ((NegS k) = Pos Z) -> Void
ZZNegisNotZ _ Refl impossible

negZeroZero: (a: ZZ) -> (a = (Pos Z)) -> (negate a = (Pos Z))
negZeroZero (Pos Z) Refl = Refl
negZeroZero (Pos (S k)) prf = void ((ZZSisNotZ k) prf)
negZeroZero (NegS k) prf = void ((ZZNegisNotZ k) prf)

negNegSIsPos: (a: ZZ) -> (a = (NegS k)) -> (-a = (Pos (S k)))
negNegSIsPos (Pos k) Refl impossible
negNegSIsPos (NegS k) Refl = Refl

negPosIsNeg: (a: ZZ) -> (a = (Pos (S k))) -> (-a = (NegS k))
negPosIsNeg (Pos Z) Refl impossible
negPosIsNeg (Pos (S k)) Refl = Refl
negPosIsNeg (NegS k) Refl impossible

|||The theorem (a=(b*c)) => ((-a)=((-b)*c)))
multNegateLeftIsNegateZ:(a:ZZ)->(b:ZZ)->(c:ZZ)->(a=(b*c))->((-a)=(-b)*c)
multNegateLeftIsNegateZ a b c prf = (rewrite (multNegateLeftZ b c) in ( numbersSameNegativesSame prf))

quotproof1: {a: ZZ} -> {b: ZZ} -> {quot: ZZ} -> (a=quot*b) -> (-a = (-quot)*b)
quotproof1 {a} {b} {quot} prf = (multNegateLeftIsNegateZ a quot b prf)

quotproof2: {a: ZZ} -> {b: ZZ} -> {quot: ZZ} -> (a=quot*b) -> (a = (-quot)*(-b))
quotproof2 {a} {b} {quot} prf = trans (prf) (sym (multNegNegNeutralZ (quot) (b)))

quotproof3: {a: ZZ} -> {b: ZZ} -> {quot: ZZ} -> (a=quot*b) -> (-a = (quot)*(-b))
quotproof3 {a} {b} {quot} prf = (multNegateRightIsNegateZ a quot b prf)

QRproof1: (a:ZZ) -> (b: ZZ) -> (a = (Pos (S k))) -> (b= (Pos (S j))) -> (quot: ZZ ** a = (quot)*b) -> (nquot: ZZ ** -a=(nquot)*b)
QRproof1 (Pos Z) b Refl Refl x impossible
QRproof1 (Pos (S k)) (Pos Z) Refl Refl x impossible
QRproof1 (Pos (S k)) (Pos (S j)) Refl Refl (quot ** pf) = ((-quot) ** quotproof1(pf))
QRproof1 (Pos (S k)) (NegS j) Refl Refl x impossible
QRproof1 (NegS k) b Refl Refl x impossible

QRproof3: (a:ZZ) -> (b: ZZ) -> (a = (Pos (S k))) -> (b= (Pos (S j))) -> (quot: ZZ ** a = (quot)*b) -> (nquot: ZZ ** a=(nquot)*(-b))
QRproof3 (Pos Z) b Refl Refl x impossible
QRproof3 (Pos (S k)) (Pos Z) Refl Refl x impossible
QRproof3 (Pos (S k)) (Pos (S j)) Refl Refl (quot ** pf) = ((-quot) ** quotproof2(pf))
QRproof3 (Pos (S k)) (NegS j) Refl Refl x impossible
QRproof3 (NegS k) b Refl Refl x impossible

QRproof4: (a:ZZ) -> (b: ZZ) -> (a = (Pos (S k))) -> (b= (Pos (S j))) -> (quot: ZZ ** a = (quot)*b) -> (quot: ZZ ** (-a)=(quot)*(-b))
QRproof4 (Pos Z) b Refl Refl x impossible
QRproof4 (Pos (S k)) (Pos Z) Refl Refl x impossible
QRproof4 (Pos (S k)) (Pos (S j)) Refl Refl (quot ** pf) = (quot ** quotproof3(pf))
QRproof4 (Pos (S k)) (NegS j) Refl Refl x impossible
QRproof4 (NegS k) b Refl Refl x impossible
