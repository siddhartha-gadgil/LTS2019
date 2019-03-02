module BoundedGCD


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
boundedGCD (S b) (S (S k)) (S Z) (LTESucc x) (LTESucc y) = S Z
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
