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

