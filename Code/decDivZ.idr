module decDivZ
import ZZ
import ZZUtils
import Divisors
import GCDZZ
import Primes
import gcd
%access public export
%default total

isDivisibleImpliesIsDivisibleZ:isDivisible a b ->
          IsDivisibleZ (Pos a) (Pos b)
isDivisibleImpliesIsDivisibleZ (n**(gpf,eqpf)) = ((Pos n)**(cong eqpf))

posIntToSuccNat:{m:ZZ}->(IsPositive m) ->(t:Nat**(((m = (Pos t)),(IsSucc t))))
posIntToSuccNat {m = (Pos (S k))} Positive = ((S k)**(Refl,(ItIsSucc )))

succGtZero:{t:Nat}->(IsSucc t)->GT t Z
succGtZero {t = (S n)} ItIsSucc = LTESucc LTEZero

rehelp2:{m:ZZ}->{k:ZZ}->(s:ZZ)-> m = k->s*k = s*m
rehelp2  s prf = rewrite sym $ prf in
              Refl

isDivisibleZImpliesIsDivisible :{a:Nat}->{b:Nat}->
     IsPositive (Pos a) -> IsDivisibleZ (Pos a) (Pos b) ->isDivisible a b
isDivisibleZImpliesIsDivisible {a = (S k)}{b = Z}  Positive x =
    void (zeroDoesntDivideNonZero PositiveZ x)
isDivisibleZImpliesIsDivisible {a = (S k)}{b = (S j)} Positive (m**eqpf) =
  (case posDivByPosIsPos {c = (Pos (S k))}{d =(Pos (S j))} Positive Positive  eqpf of
        mPos => (case posIntToSuccNat mPos of
                  (t**(equal,tsucc)) => ( t**((succGtZero tsucc),( posInjective( rewrite rehelp2 {m=m}{k=(Pos t)} (Pos (S j)) equal   in
                                                                  eqpf))))))

posSSknotOne: (Pos ( S (S k)))=1->Void
posSSknotOne Refl impossible

posSSknotMinusOne: (Pos ( S (S k)))=(-1)->Void
posSSknotMinusOne Refl impossible

gt2DoesntDivideOne: {k:Nat}->IsDivisibleZ 1 (Pos ( S (S k)))  ->Void
gt2DoesntDivideOne {k} (n**eqpf) =
  (case productOneThenNumbersOne (Pos (S (S k))) n (sym eqpf) of
        (Left (a, b)) => posSSknotOne a
        (Right (a, b)) => posSSknotMinusOne a)

succNotZ:( S n) = Z ->Void
succNotZ Refl impossible



decDivisibleZnn: (a:ZZ)->(b:ZZ)->IsNonNegative a->IsNonNegative b -> Dec (IsDivisibleZ a b)
decDivisibleZnn (Pos Z) b NonNegative y = Yes (zzDividesZero _)
decDivisibleZnn (Pos (S Z)) (Pos Z) NonNegative NonNegative = No (zeroDoesntDivideNonZero PositiveZ )
decDivisibleZnn (Pos (S Z)) (Pos (S Z)) NonNegative NonNegative= Yes ( oneDiv 1)
decDivisibleZnn (Pos (S Z)) (Pos (S (S k))) NonNegative NonNegative= No (gt2DoesntDivideOne )
decDivisibleZnn (Pos (S (S k))) (Pos Z) NonNegative NonNegative= No (zeroDoesntDivideNonZero PositiveZ )
decDivisibleZnn (Pos (S (S k))) (Pos (S j)) NonNegative NonNegative=
   (case decDiv (S (S k)) (LTESucc (LTESucc LTEZero)) (S j)
               {euc = eculidDivideAux (S(S k)) (S j) (succNotZ)} of
         (Yes prf) => (Yes (isDivisibleImpliesIsDivisibleZ prf))
         (No contra) => No(contra . (isDivisibleZImpliesIsDivisible {b =(S j)} Positive)))

|||Given two integers , a and b, it either returns a proof that  b|a or
||| a proof that b|a is impossible.
decDivisibleZ: (a:ZZ)->(b:ZZ)->(Dec (IsDivisibleZ a b))
decDivisibleZ (Pos k) (Pos j) =
  decDivisibleZnn (Pos k) (Pos j) NonNegative NonNegative
decDivisibleZ (Pos k) (NegS j) =
  (case decDivisibleZnn (Pos k) (-(NegS j)) NonNegative NonNegative of
        (Yes prf) => Yes (negativeDivides prf )
        (No contra) => No (contra . negativeDivides {d =NegS j} ))
decDivisibleZ (NegS k) (Pos j) =
  (case decDivisibleZnn (-(NegS k)) (Pos j) NonNegative NonNegative of
        (Yes prf) => Yes ( dDividesNegative prf)
        (No contra) => No (contra . dDividesNegative {a = (NegS k)}))
decDivisibleZ (NegS k) (NegS j) =
  (case decDivisibleZnn (-(NegS k)) (-(NegS j)) NonNegative NonNegative of
        (Yes prf) => Yes ( dDividesNegative (negativeDivides prf))
        (No contra) => No ( contra . doubleNegativeDivides { a =NegS k}{d = NegS j}))
