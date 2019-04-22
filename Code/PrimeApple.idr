--Applications of stuff in Primes.idr

module PrimeApple

import Primes
import NatUtils
import gcd
import Data.Fin
import NatOrder
import SriramAssRecRule

%access public export
%default total

--Prime type
isPrime : (p : Nat) -> LTE 2 p -> Type
isPrime p proofLTE = {k : Nat} -> isDivisible p k -> Either (k=1)(k=p)

--Transitivity of divisibility
transDiv : (isDivisible b a) -> (isDivisible c b) -> isDivisible c a
transDiv {a} {b} {c} (n ** pf1) (m ** pf2) = (m*n **
              (lteMultIsLTE (fst pf2) (fst pf1) ,
                rewrite (snd pf2) in
                rewrite (snd pf1) in
                rewrite sym (multAssociative a n m) in
                rewrite multCommutative n m in Refl))

--The smallest factor of a number is prime
leastDivIsPrime : (m : Nat) -> LTE 2 m ->
                  (p : Nat) -> (pGt2 : LTE 2 p) -> isDivisible m p ->
                  ((b : Nat) -> LTE b p -> (isDivisible m b) ->
                   Either (b=1)(b=p)) ->
                  isPrime p pGt2
leastDivIsPrime m mGt2 p pGt2 pDivm func = g where
  g : {k : Nat} -> isDivisible p k -> Either (k=1)(k=p)
  g {k = a} pff = func a (bDivAImpAGtB p a (fst pff) pff) (transDiv pff pDivm)

help10 : (a : Nat) -> (q : Nat) -> (S (S q)) = a ->
         (b : Nat) -> (k : Nat) -> (S (S k)) = b ->
         (prf : isDivisible a b) ->
         (lst : List Nat ** (foldList Nat 1 (*) lst = a,
           (b : NonEmpty lst ** (LTE 1 (last {ok=b} lst),
             (a = mult (head {ok=b} lst) (last {ok=b} lst),
             Either (x: LTE 2 (last {ok=b} lst) ** isPrime (last {ok=b} lst) x) (last {ok=b} lst = 1))))))
help10 a q ww b k ee prf with (prf)
    help10 a q ww b k ee prf | (m ** (pfPos , pfDiv)) =
        ([m , (S (S k))] ** (rewrite multOneRightNeutral (S k) in
                         rewrite ee in
                         rewrite multCommutative m b in (sym pfDiv),
                     (IsNonEmpty ** ((LTESucc LTEZero),
                        ((rewrite ee in
                        rewrite multCommutative m b in pfDiv),
                        Left (LTESucc (LTESucc LTEZero) **
                                leastDivIsPrime
                                (S (S q)) (LTESucc (LTESucc LTEZero))
                                (S (S k)) (LTESucc (LTESucc LTEZero))
                                (m ** (pfPos,
                                      rewrite ww in
                                      rewrite multConstantRight m ee in pfDiv))
                                (?func))
)))))

help11 : (x : Nat) -> (lst : List Nat) -> (ntMT : NonEmpty lst) ->
         last (x :: lst) = last {ok=ntMT} lst
help11 x (y :: xs) IsNonEmpty = Refl

--Factors a number into 2 other numbers, such that the
--first one is smaller and is prime (not proven yet)
--and that the list of factors folded gives back the number

--Give var as n-1
factor2 : (n : Nat) -> (var : Nat) -> (GT n 0) ->
          (lst : List Nat ** (foldList Nat 1 (*) lst = n,
            (b : NonEmpty lst ** (LTE 1 (last {ok=b} lst),
              (n = mult (head {ok=b} lst) (last {ok=b} lst),
                Either (x: LTE 2 (last {ok=b} lst) ** isPrime (last {ok=b} lst) x) (last {ok=b} lst = 1))))))
factor2 Z _ LTEZero impossible
factor2 Z _ (LTESucc _) impossible
factor2 (S Z) _ (LTESucc LTEZero) =
        ([1,1] ** (Refl, (IsNonEmpty **
                  ((LTESucc LTEZero), (Refl, Right Refl)))))
factor2 (S (S k)) Z (LTESucc LTEZero) = assert_unreachable
factor2 (S (S k)) (S Z) (LTESucc LTEZero) =
      ([(S (S k)), 1] **
       (rewrite multOneRightNeutral k in Refl,
       (IsNonEmpty ** ((LTESucc LTEZero),
          (rewrite multOneRightNeutral k in Refl, Right Refl)))))
factor2 (S (S k)) (S (S x)) (LTESucc LTEZero) =
    case decDiv (S (S k)) (LTESucc (LTESucc LTEZero)) (S (S x))
          {euc = eculidDivideAux (S (S k)) (S (S x)) (SIsNotZ)} of
     (Yes prf) => help10 (S (S k)) (k) Refl (S (S x)) (x) Refl prf
     (No contra) => factor2 (S (S k)) (S x) (LTESucc LTEZero)

--Factorises a number completely with proof of folding
factorise : (n : Nat) -> (GT n 0) ->
            (lst : List Nat ** (foldList Nat 1 (*) lst = n))
factorise Z LTEZero impossible
factorise Z (LTESucc _) impossible
factorise (S Z) (LTESucc LTEZero) = ([] ** Refl)
factorise (S (S k)) (LTESucc LTEZero) with
      (factor2 (S (S k)) (S k) (LTESucc LTEZero))
  factorise (S (S k)) (LTESucc LTEZero) |
        (lst ** (fol, (ntMT ** (lastLt, (pf2, primepf))))) = assert_total(
               (( (head {ok=ntMT} lst) ::
                  (fst (factorise (last {ok=ntMT} lst) lastLt))) **
                  (rewrite (snd (factorise (last {ok=ntMT} lst) lastLt))
                  in (sym pf2)) ))

-- creates a list with all the factors of a number upto the second argument
genFact : (n : Nat) -> Nat -> List (k : Nat ** isDivisible n k)
genFact Z Z = []
genFact Z (S k) = []
genFact (S j) Z = []
genFact (S Z) (S k) = [(S Z ** oneDiv (S Z))]
genFact (S (S j)) (S k) =
    case (decDiv (S (S j)) (LTESucc (LTESucc (LTEZero{right = j}))) (S k)
          {euc=eculidDivideAux (S (S j)) (S k) SIsNotZ }) of
               (Yes prf) => (genFact (S (S j)) k) ++ [(S k ** prf)]
               (No contra) => (genFact (S (S j)) k)


--if the List has only 2 elements, i.e 1 and p, then the number is prime. the function outputs a list (secretly genFact)
-- along with the proof that the length of the list of factors is 2
isPrimeWithoutProof : (p: Nat) -> {auto pf: LTE 2 p} -> Type
isPrimeWithoutProof p = length (genFact p p) = 2

-- more than 2 factors implies number is composite
isCompositeWithoutProof : (n: Nat) -> {auto pf: LTE 2 n} -> Type
isCompositeWithoutProof n = Prelude.Nat.GT (Prelude.List.length (genFact n n)) 2

-- Two is a prime
twoPr : (isPrime 2 (LTESucc (LTESucc (LTEZero {right =0}))))
twoPr {k=Z} (x ** pf) = void (SIsNotZ (snd pf))
twoPr {k=(S Z)} (x ** pf) = Left Refl
twoPr {k=(S (S Z))} (x ** pf) = Right Refl
twoPr {k=(S (S (S k)))} pf = void (bGtAImpNotbDivA 2 (S (S (S k))) k (LTESucc (LTESucc (LTESucc (LTEZero {right = k})))) (pf))

--Composite proof
isComposite : (n : Nat) -> LTE 2 n -> Type
isComposite n pflte = (a : Nat ** (b : Nat ** ((GT a 1, GT b 1), n = a*b)))

-- --deciability for Composite numbers
-- decComposite : (n: Nat) -> (pf : LTE 2 n) -> Dec (isComposite n pf)
-- decComposite Z LTEZero impossible
-- decComposite Z (LTESucc _) impossible
-- decComposite (S Z) (LTESucc LTEZero) impossible
-- decComposite (S Z) (LTESucc (LTESucc _)) impossible
-- decComposite (S (S k)) pf = ?decCompositerhs_1
--
--


--if 1<n, a not equal to a*n
aNotEqToMultA : (a : Nat) -> LTE 1 a -> (n : Nat) -> LTE 2 n -> (a = a*n) -> Void
aNotEqToMultA _ _ Z LTEZero _ impossible
aNotEqToMultA _ _ Z (LTESucc _) _ impossible
aNotEqToMultA _ _ (S Z) (LTESucc LTEZero) _ impossible
aNotEqToMultA _ _ (S Z) (LTESucc (LTESucc _)) _ impossible
aNotEqToMultA Z LTEZero (S (S _)) _ _ impossible
aNotEqToMultA Z (LTESucc _) (S (S _)) _ _ impossible
aNotEqToMultA (S j) (LTESucc (LTEZero {right = j})) (S (S k)) (LTESucc (LTESucc (LTEZero {right = k}))) prf =
                              SIsNotZ {x = j+(k*(S j))} (sym (pfeq)) where
                                pfeq  = plusLeftCancel (S j) Z ((S k)*(S j)) pfeq1 where
                                  pfeq1 = rewrite (multCommutative (S (S k)) (S j)) in
                                          trans (plusZeroRightNeutral (S j)) prf

--helper apNat function
apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl

--n is not both prime and composite
notBothPrimeandComp : {n : Nat} -> (pf : LTE 2 n) -> Not (isPrime n pf, isComposite n pf)
notBothPrimeandComp {n = Z} LTEZero _ impossible
notBothPrimeandComp {n = Z} (LTESucc _) _ impossible
notBothPrimeandComp {n = (S Z)} (LTESucc LTEZero) _ impossible
notBothPrimeandComp {n = (S Z)} (LTESucc (LTESucc _)) _ impossible
notBothPrimeandComp {n = (S (S k))} pftwolten (pfprime , (a ** (b ** ((pfagtone, pfbgtone), pfneqab)))) =
                            void (aNotEqToMultA (S (S k)) (lteTransitive (LTESucc (LTEZero {right = (S Z)})) pftwolten) b pfbgtone pfeq) where
                              pfeq = (trans pfneqab funceq) where
                                funceq = (apNat (\x=>(x*b)) a (S (S k)) pfaeqn) where
                                  pfaeqn =  case (pfprime (b ** ((lteTransitive (LTESucc (LTEZero {right = (S Z)})) pfbgtone), pfneqab))) of
                                          Left pf => void ((Prelude.Basics.fst (ltImpliesNotEqNotGT {a=(S Z)} {b = a} pfagtone)) (sym pf))
                                          Right pf => pf


-- generates a list of numbers from 2 to n-1
listGen : (n: Nat) -> List Nat
listGen Z = []
listGen (S Z) = []
listGen (S (S Z)) = []
listGen (S (S (S k))) = listGen (S (S k)) ++ [S (S k)]

--Since 1 and p already divide p, we just have to make sure that numbers between 2 and n-1 either divide or don't divide n




-- given n >= 2, it is either prime or Composite
eitherPrimeOrComp : {n : Nat} -> (pf : LTE 2 n) -> Either (isPrime n pf)(isComposite n pf)
eitherPrimeOrComp {n = Z} LTEZero impossible
eitherPrimeOrComp {n = Z} (LTESucc _) impossible
eitherPrimeOrComp {n = (S Z)} (LTESucc LTEZero) impossible
eitherPrimeOrComp {n = (S Z)} (LTESucc (LTESucc _)) impossible
eitherPrimeOrComp {n = (S (S k))} pflte = case (Prelude.List.length (genFact (S (S k)) (S (S k)))) of
                                (S (S Z)) => ?pfprme
                                otherwise => Right (Prelude.Pairs.DPair.fst (fromMaybe (S Z ** oneDiv (S (S k))) (index' (S Z) (genFact (S (S k)) (S (S k))))) ** (fst (Prelude.Pairs.DPair.snd (fromMaybe (S Z ** oneDiv (S (S k))) (index' (S Z) (genFact (S (S k)) (S (S k)))))) ** ((?agt1, ?bgt1), snd (snd (Prelude.Pairs.DPair.snd (fromMaybe (S Z ** oneDiv (S (S k))) (index' (S Z) (genFact (S (S k)) (S (S k))))))))))
