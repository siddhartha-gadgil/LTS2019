module ZZUtils
import ZZ
import NatUtils
%access public export
%default total

data IsNonNegative : ZZ->Type where
 NonNegative :(IsNonNegative (Pos k))

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

data NotBothZeroZ :ZZ->ZZ->Type where
  LeftPositive :NotBothZeroZ (Pos (S k)) m
  LeftNegative :NotBothZeroZ (NegS k) m
  RightPositive :NotBothZeroZ m (Pos (S k))
  RightNegative :NotBothZeroZ m (NegS k)

