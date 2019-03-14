module BoundedGCD
import ZZ
import ZZUtils
import Divisors


%default total
%access public export

notLTEimpliesLT : (a: Nat) -> (b: Nat) -> (LTE a b -> Void) -> LTE (S b) a
notLTEimpliesLT Z b contra = void (contra (LTEZero))
notLTEimpliesLT (S k) Z f = LTESucc (LTEZero)
notLTEimpliesLT (S k) (S j) contra =
  LTESucc (notLTEimpliesLT k j previousContra) where
    previousContra = \evidence : (LTE k j) => contra (LTESucc evidence)

subWithBound: (n: Nat) -> (m: Nat) -> (LTE m n) -> (k: Nat ** LTE k n)
subWithBound n Z LTEZero = (n ** lteRefl)
subWithBound (S p) (S q) (LTESucc pf) = case subWithBound p q pf of
                                             (x ** pf) =>
                                                (x ** lteSuccRight pf)

boundedGCD : (bnd: Nat) -> (n: Nat) -> (m: Nat) -> (LTE n bnd) -> (LTE (S m) bnd) -> Nat
boundedGCD (S b) Z m x (LTESucc y) = m
boundedGCD (S b) (S k) Z x (LTESucc y) = (S k)
boundedGCD (S b) (S Z) (S j) (LTESucc x) (LTESucc y) = S Z
boundedGCD (S b) (S k) (S Z) (LTESucc x) (LTESucc y) = S Z
boundedGCD (S b) (S (S (k))) (S (S (j))) (LTESucc x) (LTESucc y) =
  case isLTE j k of
        (Yes prf) => case subWithBound k j prf of
                           (diff ** pf) => boundedGCD b (S (S j)) diff y (lteTransitive (LTESucc pf) x)
        (No contra) =>
          let
            ineq = notLTEimpliesLT j k contra
          in
            boundedGCD b (S (S j)) (S (S k)) y (lteTransitive (LTESucc (LTESucc ineq)) y)

gcdAlgo : Nat -> Nat -> Nat
gcdAlgo k j = case isLTE (S j) k of
                   (Yes prf) => boundedGCD k k j lteRefl prf
                   (No contra) =>
                      let
                        ineq = notLTEimpliesLT (S j) k contra
                      in
                        boundedGCD (S j) k j  (lteSuccLeft ineq) lteRefl



|||Given a proof that m<=n, returns n-m with proof that k = n-m<=n and
|||(Pos k)=(Pos n)+(-(Pos m) as integers
subWithBoundZ: (n: Nat) -> (m: Nat) -> (LTE m n) -> (k: Nat ** ((LTE k n),((Pos k)=(Pos n)+(-(Pos m)))))
subWithBoundZ n Z LTEZero = (n ** (lteRefl,rewrite plusZeroRightNeutralZ (Pos n) in
                                              Refl))
subWithBoundZ (S p) (S q) (LTESucc pf) = case subWithBoundZ p q pf of
                                             (x ** (pf,subpf)) =>
                                                (x ** (lteSuccRight pf,
                                                    (subSuccSuccNeutrtalZ subpf)))
|||Rewrites n = a + (-m) as a = n+ (1*m)
simpleRewrite:{n:ZZ}->{a:ZZ}->{m:ZZ}->(n= a+(-m))->(a= n +(1*m))
simpleRewrite prf {a}{n}{m} = rewrite sym $ plusZeroLeftNeutralZ a in
                        rewrite multOneLeftNeutralZ m in
                        rewrite sym $ plusNegateInverseLZ m in
                        rewrite plusCommutativeZ n m in
                        rewrite sym $ plusAssociativeZ m (-m) a in
                        rewrite plusCommutativeZ (-m) a in
                        cong (sym prf)

|||If n = a+ (-m), then gcd (m,n) = gcd (a,m)
helperboundedGCDZ:{n:ZZ}->{m:ZZ}->GCDZ m n d->
    (n= a+(-m))->GCDZ a m d
helperboundedGCDZ x prf = euclidConservesGcdWithProof {quot = (1)}  (simpleRewrite prf) x

||| Proves that Pos (k)+ (- (Pos (j)) = minusNatZ k j
simplerewrite2:{k:Nat}->{j:Nat}-> Pos (k)+ (- (Pos (j))) = minusNatZ k j
simplerewrite2 {k = k}{j = Z}= rewrite plusZeroRightNeutralZ (Pos k) in Refl
simplerewrite2 {k = k}{j = (S j)}= Refl

||| Proves that NotBothZero Z m implies (Pos m) is positive
notBothZeroZeroNatPos:{m:Nat}->NotBothZero Z m -> (IsPositive (Pos m))
notBothZeroZeroNatPos {m = (S k)} RightIsNotZero = Positive

|||A bounded GCD function that given a bound and natural numbers n and m such that
|||n and m are not both zero, returns gcd((Pos n),(Pos m)) with proof
boundedGCDZ : (bnd: Nat) -> (n: Nat) -> (m: Nat) -> (LTE n bnd) -> (LTE (S m) bnd)->
    (NotBothZero n m) -> (d:ZZ**GCDZ (Pos n) (Pos m) d)
boundedGCDZ (S b) Z m x (LTESucc y) nbz = ((Pos m)**(gcdSymZ (gcdOfZeroAndInteger (Pos m) (notBothZeroZeroNatPos nbz)) ))
boundedGCDZ (S b) (S k) Z x (LTESucc y) nbz = (Pos (S k)**gcdOfZeroAndInteger (Pos (S k)) Positive)
boundedGCDZ (S b) (S Z) (S j) (LTESucc x)  (LTESucc y) nbz = (1 **(gcdSymZ (gcdOfOneAndInteger (Pos (S j)))))
boundedGCDZ (S b) (S k) (S Z) (LTESucc x) (LTESucc y) nbz = (1 **(gcdOfOneAndInteger (Pos (S k))))
boundedGCDZ (S b) (S (S (k))) (S (S (j))) (LTESucc x) (LTESucc y) nbz =
  case isLTE j k of
        (Yes prf) => case subWithBoundZ k j prf of
                           (diff ** (pf,subpf)) => (case boundedGCDZ b (S (S j)) diff y (lteTransitive (LTESucc pf) x) LeftIsNotZero of
                             (d**gcdpf) => (d**(helperboundedGCDZ  gcdpf  (rewrite sym $simplerewrite2 {k=k}{j=j} in subpf))))
        (No contra) =>
           let
             ineq = notLTEimpliesLT j k contra
           in
             (case boundedGCDZ b (S (S j)) (S (S k)) y (lteTransitive (LTESucc (LTESucc ineq)) y) LeftIsNotZero of
               (d**gcdpf) => (d** (gcdSymZ gcdpf)))

|||A helper for bezReplace which does the rewrite as indicated in its type.
helperbezReplace:{v:ZZ}->{u:ZZ}->{j:Nat}->{diff:Nat}->{d:ZZ}->{k:Nat}->
       d =  ( u *(Pos (S (S j)))) + ( v*(Pos diff))->(Pos diff) = (Pos k )+(-(Pos j))->
         d=(u*(Pos (S (S j)))) + (v * ((Pos k) + (-(Pos j))))
helperbezReplace prf prf1 = rewrite sym $ prf1 in prf

|||A helper function for boundedGCDbez which does the rewrite as indicated in its type.
bezReplace:{v:ZZ}->{u:ZZ}->{j:Nat}->{diff:Nat}->{d:ZZ}->{k:Nat}->
       d =  ( u *(Pos (S (S j)))) + ( v*(Pos diff))->(Pos diff) = (Pos k )+(-(Pos j))->
                        d=v*(Pos (S(S k))) +(u+(-v))*(Pos (S (S j)))
bezReplace {v}{u}{j}{diff}{k} prf prf1 = rewrite plusCommutativeZ (v*(Pos (S(S k)))) ((u+(-v))*(Pos (S (S j)))) in
                                         rewrite plusCommutativeZ u (-v) in
                                         rewrite multDistributesOverPlusLeftZ  (-v) u (Pos (S (S j))) in
                                         rewrite multNegateLeftZ v (Pos (S (S j))) in
                                         rewrite sym $ multNegateRightZ v  (Pos (S (S j))) in
                                         rewrite sym $ plusAssociativeZ (v*(NegS (S j))) (u*(Pos (S (S j)))) (v*(Pos (S (S k)))) in
                                         rewrite plusCommutativeZ (u*(Pos (S (S j)))) (v*(Pos (S (S k)))) in
                                         rewrite plusAssociativeZ (v*(NegS (S j))) (v*(Pos (S (S k)))) (u*(Pos (S (S j)))) in
                                         rewrite sym $multDistributesOverPlusRightZ v (NegS (S j)) (Pos (S (S k))) in
                                         rewrite plusCommutativeZ  (v*(minusNatZ k j)) (u* (Pos (S (S j)))) in
                                         rewrite sym $ simplerewrite2 {k=k}{j=j}in
                                         helperbezReplace prf prf1

|||A bounded GCD function that given a bound and natural numbers n and m such that
|||n and m are not both zero, returns gcd((Pos n),(Pos m)) and bezout coefficients
|||with proof that it is the gcd and proof that it is a linear combination of
|||(Pos n) and (Pos m)
boundedGCDbez : (bnd: Nat) -> (n: Nat) -> (m: Nat) -> (LTE n bnd) -> (LTE (S m) bnd)->
    (NotBothZero n m) -> (d**((GCDZ (Pos n) (Pos m) d),(u:ZZ**v:ZZ**(d=(u*(Pos n))+(v*(Pos m))))))
boundedGCDbez (S b) Z m x (LTESucc y) nbz = ((Pos m)**((gcdSymZ (gcdOfZeroAndInteger (Pos m) (notBothZeroZeroNatPos nbz))),
                                                                  (0**1**(rewrite multOneLeftNeutralZ (Pos m) in Refl))))
boundedGCDbez (S b) (S k) Z x (LTESucc y) nbz = ((Pos (S k))**((gcdOfZeroAndInteger (Pos (S k)) Positive),(1**0**(   rewrite plusZeroRightNeutral k in
                                                                                                                     rewrite plusZeroRightNeutral k in
                                                                                                                        Refl))))
boundedGCDbez (S b) (S Z) (S j) (LTESucc x)  (LTESucc y) nbz = (1 **((gcdSymZ (gcdOfOneAndInteger (Pos (S j)))),(1**0**Refl)))
boundedGCDbez (S b) (S k) (S Z) (LTESucc x) (LTESucc y) nbz = (1 **((gcdOfOneAndInteger (Pos (S k))),(0**1**Refl)))
boundedGCDbez (S b) (S (S (k))) (S (S (j))) (LTESucc x) (LTESucc y) nbz =
  case isLTE j k of
        (Yes prf) => case subWithBoundZ k j prf of
                           (diff ** (pf,subpf)) => (case boundedGCDbez b (S (S j)) diff y (lteTransitive (LTESucc pf) x) LeftIsNotZero of
                             (d**(gcdpf,(u**v**eqpf))) => (d**((helperboundedGCDZ  gcdpf  (rewrite sym $simplerewrite2 {k=k}{j=j} in subpf)),
                                (v**(u+(-v)**( bezReplace eqpf subpf))))))
        (No contra) =>
           let
             ineq = notLTEimpliesLT j k contra
           in
             (case boundedGCDbez b (S (S j)) (S (S k)) y (lteTransitive (LTESucc (LTESucc ineq)) y) LeftIsNotZero of
               (d**(gcdpf,(u**v**eqpf))) => (d** ((gcdSymZ gcdpf), (v**u**
                                                rewrite plusCommutativeZ (v*(Pos (S (S k)) )) (u*(Pos (S (S j)) )) in
                                                  eqpf))))
