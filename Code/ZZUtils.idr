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

|||Proof that positive numbers are not zero
posThenNotZero:{a:ZZ}->(IsPositive a)->(NotZero a)
posThenNotZero {a = (Pos (S k))} Positive = PositiveZ

|||Rewrites a=b as a=1*b
rewriteRightAsOneTimesRight: {a:ZZ}->{b:ZZ}->(a=b)->(a=(1*b))
rewriteRightAsOneTimesRight {a}{b}prf = rewrite ( (multOneLeftNeutralZ b)) in prf

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
