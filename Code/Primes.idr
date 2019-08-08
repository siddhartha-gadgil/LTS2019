module Primes

import NatUtils
import gcd
import Data.Fin
import NatOrder
import SriramAssRecRule

%access public export
%default total


--isDivisible a b can be constucted if b divides a
isDivisible : Nat -> Nat -> Type
isDivisible a b = (n : Nat ** (GT n 0, a = b * n))

--1 divides everything
oneDiv : (a : Nat) -> {auto x : GT a 0} -> isDivisible a 1
oneDiv a {x=pf} = (a ** (pf , rewrite plusZeroRightNeutral a in Refl))

--If 1|a => 1*c | a*c
mulDiv : (a, c : Nat) -> {auto pf1 : GT a 0} -> {auto pf2 : GT c 0} ->
  isDivisible a 1 -> isDivisible (a * c) c
mulDiv a c {pf1=p} x = (a ** (p ,rewrite multCommutative a c in Refl))

--Either(a=b)(_) <=> Either (S a = S b)(_)
help1 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT (S a) (S b)) (LT (S b) (S a))) ->
  Either (S a = S b) (Either (LT (S a) (S b)) (LT (S b) (S a)))
help1 {a} {b} (Left l) = Left (eqSucc a b l)
help1 (Right r) = Right r

--Either(_)(Either(Sa<Sb)(_)) <=> Either (_)(Either(a<b)(_))
help2 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT a b) (LT (S b) (S a))) ->
  Either (a = b) (Either (LT (S a) (S b)) (LT (S b) (S a)))
help2 (Left l) = Left l
help2 {a} {b} (Right (Left l)) = Right(Left (LTESucc l))
help2 (Right (Right r)) = Right (Right r)

--Either(_)(Either(_)(Sb<Sa)) <=> Either (_)(Either(_)(b<a))
help3 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT a b) (LT b a)) ->
  Either (a = b) (Either (LT a b) (LT (S b) (S a)))
help3 (Left l) = Left l
help3 (Right (Left l)) = Right(Left l)
help3 {a} {b} (Right (Right r)) = Right (Right (LTESucc r))

|||Either a = b, a < b, or a > b
totOrdNat : (a : Nat) -> (b : Nat) ->
  Either (a = b) (Either (LT a b) (LT b a))
totOrdNat Z Z = Left Refl
totOrdNat Z (S k) = Right (Left (LTESucc LTEZero))
totOrdNat (S k) Z = Right (Right (LTESucc LTEZero))
totOrdNat (S k) (S j) = help1 (help2 (help3 (totOrdNat k j)))

--LTE a b => LTE a*n b*n
multRightLTE : (a,b : Nat) -> (n : Nat) -> GT n 0 ->
  LTE a b -> LTE (a*n) (b*n)
multRightLTE a b (S Z) (LTESucc LTEZero) lteab =
                            rewrite multOneRightNeutral a in
                            rewrite multOneRightNeutral b in
                            lteab
multRightLTE a b (S (S k)) (LTESucc LTEZero{right=(S k)}) lteab =
          rewrite multRightSuccPlus a (S k) in
          rewrite multRightSuccPlus b (S k) in
          ltePlusIsLTE lteab
          (multRightLTE a b (S k) (LTESucc LTEZero{right=k}) lteab)

--If a = b*n, b <= a
aEqProdImpAGtB : (a,b,n : Nat) -> GT n 0 -> (a = b*n) -> LTE b a
aEqProdImpAGtB _ _ Z LTEZero _ impossible
aEqProdImpAGtB _ _ Z (LTESucc _) _ impossible
aEqProdImpAGtB (b * (S k)) b (S k) x Refl = case b of
              Z => LTEZero
              (S m) =>
                rewrite sym (multOneLeftNeutral (S m)) in
                rewrite multCommutative (S m) (S k) in
                rewrite multDistributesOverPlusRight k (S Z) m in
                rewrite plusCommutative (k*1) (k*m) in
                rewrite plusAssociative m (k*m) (k*1) in
                rewrite plusCommutative (m + k*m) (k*1) in
                rewrite sym (multDistributesOverPlusRight (S k) 1 m) in
                multRightLTE 1 (S k) (S m) (LTESucc (LTEZero)) x

--If b | a => b <= a
bDivAImpAGtB : (a,b,n : Nat) -> isDivisible a b -> LTE b a
bDivAImpAGtB a b n (x ** pf) = case (fst pf) of
              (LTESucc LTEZero{right=k}) => aEqProdImpAGtB a b (S k) (fst pf) (snd pf)

--GT implies Not LTE
gtImpliesNotLTE : GT a b -> Not (LTE a b)
gtImpliesNotLTE {a=Z} {b=_} LTEZero impossible
gtImpliesNotLTE {a=Z} {b=_} (LTESucc _) impossible
gtImpliesNotLTE {a=(S k)} {b=Z} x = case isLTE (S k) Z of
                                 (Yes prf) => absurd
                                 (No contra) => contra
gtImpliesNotLTE {a=(S k)} {b=(S j)} x = case isLTE (S k) (S j) of
                                 (Yes prf) => void
                                      (gtImpliesNotLTE (fromLteSucc x) (fromLteSucc prf))
                                 (No contra) => contra

--If b > a => b does not divide a
bGtAImpNotbDivA : (a,b,n : Nat) -> GT b a -> (isDivisible a b -> Void)
bGtAImpNotbDivA a b n x = impliesContrapositive
                          (isDivisible a b)
                          (LTE b a)
                          (bDivAImpAGtB a b n)
                          (gtImpliesNotLTE x)

--(S (S k)) = 0 is not possible
zNotEqSS : (k : Nat) -> ((S (S k)) = 0 -> Void)
zNotEqSS Z = absurd
zNotEqSS (S k) = absurd

--isDivisible p 0 => (S (S k)) = 0
help4 : (p : Nat) -> LTE 2 p -> isDivisible p 0 -> p = 0
help4 Z LTEZero _ impossible
help4 Z (LTESucc _) _ impossible
help4 (S Z) (LTESucc LTEZero) _ impossible
help4 (S Z) (LTESucc (LTESucc _)) _ impossible
help4 (S (S k)) (LTESucc (LTESucc LTEZero)) x = snd (snd x)


--If x = 0, and p >= 2, x cannot divide p
zNotDivp : (p : Nat) -> LTE 2 p -> ((isDivisible p 0) -> Void)
zNotDivp Z LTEZero impossible
zNotDivp Z (LTESucc _) impossible
zNotDivp (S Z) (LTESucc LTEZero) impossible
zNotDivp (S Z) (LTESucc (LTESucc _)) impossible
zNotDivp (S (S k)) (LTESucc (LTESucc LTEZero)) =
                        impliesContrapositive
                        (isDivisible (S (S k)) 0)
                        ((S (S k)) = 0)
                        (help4 (S (S k)) (LTESucc (LTESucc LTEZero)))
                        (zNotEqSS k)

-- Helping out metaHelp
metaMetaHelp5 : (j : Nat) -> (S (j+0)) = (S j)
metaMetaHelp5 Z = Refl
metaMetaHelp5 (S k) = rewrite plusZeroRightNeutral k in Refl

--Helping out help5
metaHelp5 : (S (S k)) = (S (j+0)) -> (S (S k)) = (S (j))
metaHelp5 {j} prf = rewrite sym (metaMetaHelp5 j) in prf


-- Helping out the absurd case
help5: (S (S k)) = (S (j+0)) -> LT (S j) (S (S k)) ->  LTE (S Z) 0
help5 {k} {j} prf x = lteMinusConstantRight {c=(S j)}
            (rewrite sym (metaMetaHelp5 j) in
             rewrite sym prf in
             rewrite eqSucc (S (S k)) (S j) (metaHelp5 prf) in
             x)

--If a divides b => b=a*n
bDivAImpBEqAN : (a,b : Nat) -> isDivisible b a ->  (k : Nat ** b = a * k)
bDivAImpBEqAN a b (p ** (proofGT, proofEq)) = (p ** proofEq)

--To help out help6
metaHelp6 : (p : Nat) -> (x : Nat) -> (c : Nat) ->
  (p = x*c) -> q = c -> (p = q*x)
metaHelp6 p x c prf prf1 = rewrite prf1 in
                       rewrite multCommutative c x in prf

--To help out a case in notDivIfRem
help6 : (p : Nat) -> (x : Nat) -> (c : Nat) ->
  (p = q*x) -> (p = (S r) + q*x) ->
  (Z = (S r))
help6 p x c {q} {r} p1 p2 = plusRightCancel Z (S r) (q*x) (trans (sym p1) p2)

--To help out another case of notDivIfRem
help7 : (p : Nat) -> (x : Nat) -> (c : Nat) -> (k : Nat) -> (r : Nat) ->
        c + k = q -> p = x*c -> p = (S r) + q*x ->
        Z = (S r) + k*x
help7 p x c k r pfSum pfMul pfRem =
          plusRightCancel Z ((S r)+k*x) (c*x)
          (rewrite sym (plusAssociative (S r) (k*x) (c*x)) in
           rewrite plusCommutative (k*x) (c*x) in
           rewrite sym (multDistributesOverPlusLeft c k x) in
           rewrite pfSum in
           rewrite sym (multCommutative x c) in
           rewrite sym (pfMul) in pfRem)

--Helper for help8
metahelp8 : (x : Nat) -> (S q) + k = c -> x +(q+k)*x = c*x
metahelp8 x prf = rewrite sym prf in Refl

--Last case!
help8 : (p : Nat) -> (x : Nat) -> (c : Nat) -> (k : Nat) ->
        (m : Nat) -> (r : Nat) -> (q : Nat) ->
        (S q) + k = c -> (S (S r)) + m = x -> p = x*c -> p = (S r) + q*x ->
        Z = k*(S r) + (S k)*(S m)
help8 p x c k m r q qLtc srLtx pfMul pfRem =
          plusLeftCancel (S r) Z (k*(S r) + (S k)*(S m))
          (rewrite plusAssociative (S r) (k*(S r)) ((S k)*(S m)) in
           rewrite sym (multDistributesOverPlusRight (S k) (S r) (S m)) in
           rewrite plusAssociative r (S Z) m in
           rewrite plusCommutative r (S Z) in
           rewrite srLtx in
           rewrite sym (plusCommutative (k*x) ((S (S r)) + m)) in
           rewrite srLtx in
           rewrite plusCommutative (k*x) x in
           rewrite plusZeroRightNeutral r in
           plusLeftCancel (q*x) (S r) (x + k*x)
           (rewrite plusAssociative (q*x) x (k*x) in
            rewrite plusCommutative (q*x) x in
            rewrite sym (multDistributesOverPlusLeft (S q) k x) in
            rewrite metahelp8 {q=q} {k=k} {c=c} x qLtc in
            rewrite (multCommutative c x) in
            rewrite sym pfMul in
            rewrite plusCommutative (q*x) (S r) in
            (sym pfRem)))

help9 : (k,r,m : Nat) ->
        Z = k*(S r) + (S k)*(S m) -> Z = (S k)*(S m) + k*(S r)
help9 k r m prf = rewrite plusCommutative ((S k)*(S m)) (k*(S r)) in prf

--To help out the last case, by creating a term of an uninhabited type
notDivIfRem : (p : Nat) -> (x : Nat) -> (r : Nat) -> {q : Nat} ->
  (p = (S r) + q*x) -> LT (S r) x ->
  (c : Nat ** p = x * c) -> Void
notDivIfRem p x r {q=q} prfRem prfLt (c ** prfDiv) =
    case decEq q c of
        (Yes prf) => absurd $
                      (help6 p x c (metaHelp6 p x c prfDiv prf) prfRem)
        (No contra) => case totOrdNat q c of
              (Left l) => void (contra l)
              (Right (Left qLtc)) => case (lteToLEQ qLtc) of
                        (k ** pf1) => case (lteToLEQ prfLt) of
                          (m ** pf2) => absurd $
                              help9 k r m
                                (help8 p x c k m r q pf1 pf2 prfDiv prfRem)
              (Right (Right qGtc)) => case (lteToLEQ (lteSuccLeft qGtc)) of
                          (k ** pf) => absurd $
                              (help7 p x c k r pf prfDiv prfRem)

--The usual case for divisibility
usual : (p : Nat) -> LTE 2 p -> (x : Nat) -> (LT 0 x) -> (LT x p) ->
  (euc : (q : Nat ** (r : Nat ** ((p = r + (q * x)), LT r x)))) ->
  Dec (isDivisible p x)
usual Z LTEZero _ _ _ _ impossible
usual Z (LTESucc _) _ _ _ _ impossible
usual (S Z) (LTESucc LTEZero) _ _ _ _ impossible
usual (S Z) (LTESucc (LTESucc _)) _ _ _ _ impossible
usual (S (S _)) (LTESucc (LTESucc LTEZero)) Z LTEZero _ _ impossible
usual (S (S _)) (LTESucc (LTESucc LTEZero)) Z (LTESucc _) _ _ impossible
usual (S (S k)) (LTESucc (LTESucc LTEZero))
      (S j) (LTESucc LTEZero)
      xLtp euc with (euc)
        usual (S (S k)) (LTESucc (LTESucc LTEZero))
              (S j) (LTESucc LTEZero)
              xLtp euc | (Z ** (Z ** (pf,_))) = absurd $ pf

        usual (S (S k)) (LTESucc (LTESucc LTEZero))
              (S j) (LTESucc LTEZero)
              xLtp euc | ((S Z) ** (Z ** (pf,_))) = absurd $
                      (help5 pf xLtp)

        usual (S (S k)) (LTESucc (LTESucc LTEZero))
              (S j) (LTESucc LTEZero)
              xLtp euc | ((S (S b)) ** (Z ** (pf,_))) =
                Yes ((S (S b)) ** ((LTESucc LTEZero),
                                    (rewrite multCommutative (S j) (S (S b)) in pf)))

        usual (S (S k)) (LTESucc (LTESucc LTEZero))
              (S j) (LTESucc LTEZero)
              xLtp euc | (_ ** ((S a) ** (pf1,pf2))) = No
                              (impliesContrapositive
                                (isDivisible (S (S k)) (S j))
                                (c : Nat ** (S (S k)) = (S j) * c)
                                (bDivAImpBEqAN (S j) (S (S k)))
                                (notDivIfRem (S (S k)) (S j) a pf1 pf2))


--Decidability for divisibility
decDiv : (p : Nat) -> LTE 2 p -> (x : Nat) ->
  {euc : (q : Nat ** (r : Nat ** ((p = r + (q * x)), LT r x)))} ->
  Dec (isDivisible p x)
decDiv Z LTEZero _ impossible
decDiv Z (LTESucc _) _ impossible
decDiv (S Z) (LTESucc LTEZero) _ impossible
decDiv (S Z) (LTESucc (LTESucc _)) _ impossible
decDiv (S (S k)) (LTESucc (LTESucc LTEZero)) x {euc=big} =
    case totOrdNat (S (S k)) x of
      (Left l) => Yes (1 ** ((LTESucc LTEZero),
                             rewrite l in
                             rewrite sym (multOneRightNeutral x) in
                             Refl))
      (Right (Left l)) => No (bGtAImpNotbDivA
                              (S (S k)) x
                              (divNatNZ x (S (S k)) SIsNotZ)
                              l)
      (Right (Right r)) => case x of
          Z => No (zNotDivp (S (S k)) (LTESucc (LTESucc LTEZero)))
          (S m) => usual (S (S k)) (LTESucc (LTESucc LTEZero)) (S m)
                   (LTESucc LTEZero) r big
