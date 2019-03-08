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




subWithBoundZ: (n: Nat) -> (m: Nat) -> (LTE m n) -> (k: Nat ** ((LTE k n),((Pos k)=(Pos n)+(-(Pos m)))))
subWithBoundZ n Z LTEZero = (n ** (lteRefl,rewrite plusZeroRightNeutralZ (Pos n) in
                                              Refl))
subWithBoundZ (S p) (S q) (LTESucc pf) = case subWithBoundZ p q pf of
                                             (x ** (pf,subpf)) =>
                                                (x ** (lteSuccRight pf,
                                                    (subSuccSuccNeutrtalZ subpf)))

simpleRewrite:{n:ZZ}->{a:ZZ}->{m:ZZ}->(n= a+(-m))->(a= n +(1*m))
simpleRewrite prf {a}{n}{m} = rewrite sym $ plusZeroLeftNeutralZ a in
                        rewrite multOneLeftNeutralZ m in
                        rewrite sym $ plusNegateInverseLZ m in
                        rewrite plusCommutativeZ n m in
                        rewrite sym $ plusAssociativeZ m (-m) a in
                        rewrite plusCommutativeZ (-m) a in
                        cong (sym prf)





helperboundedGCDZ:{n:ZZ}->{m:ZZ}->GCDZ m n d->
    (n= a+(-m))->GCDZ a m d
helperboundedGCDZ x prf = euclidConservesGcdWithProof {quot = (1)}  (simpleRewrite prf) x

simplerewrite2:{k:Nat}->{j:Nat}-> Pos (k)+ (- (Pos (j))) = minusNatZ k j
simplerewrite2 {k = k}{j = Z}= rewrite plusZeroRightNeutralZ (Pos k) in Refl
simplerewrite2 {k = k}{j = (S j)}= Refl

notBothZeroZeroNatPos:{m:Nat}->NotBothZero Z m -> (IsPositive (Pos m))
notBothZeroZeroNatPos {m = (S k)} RightIsNotZero = Positive

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
