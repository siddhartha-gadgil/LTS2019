module Mergesort

import Data.Vect

import LectureEvens

-- import SortingWithProof

total
NatVect : Nat -> Type
NatVect n = Vect n Nat

total
SortProof : (n : Nat) -> (NatVect n) -> (Fin n) -> Type
SortProof Z v a impossible
SortProof (S k) v l = LTE (Vect.index (pred l) v) (Vect.index l v)

total
IsSorted : (n : Nat) -> (v : (NatVect n)) -> Type
IsSorted n v = (k : Fin n) -> (SortProof n v k)

--Takes the first m elements from a vector
Vecttake : (m:Nat)->Vect n elem -> LTE m n -> Vect m  elem
Vecttake Z xs LTEZero = []
Vecttake (S k) (x::xs) (LTESucc pf) = x::(Vecttake k xs pf)

--Takes the last m elements from a vector
Vecttakefromlast :(m:Nat)->Vect n elem -> LTE m n ->Vect m elem
Vecttakefromlast m xs pf = reverse (Vecttake  m (reverse xs) pf)

-- Inserts an element at the end of the vector
insertend : (x:elem)->Vect n elem->Vect (S n) elem
insertend x [] = [x]
insertend x (y :: xs) = y::(insertend x xs)

--apNat as defined in class. Lemma that proves that if n = m, then f(n) = f(m)
-- apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
-- apNat f m m Refl = Refl

--defined in class. Returns n/2 if n is even
-- half : (n: Nat) -> IsEven n -> Nat
-- half Z ZEven = 0
-- half (S (S k)) (SSEven k x) = S (half k x)

--returns (n - 1)/2 if (n + 1) is odd
halfnMinusone : (n : Nat) -> (IsEven (S n)) -> Nat
halfnMinusone (S Z) (SSEven Z ZEven) = Z
halfnMinusone (S (S k)) (SSEven (S k) pf) = S(halfnMinusone k pf)

-- lemma that proves that n is LTE S n
nLTESn : (n : Nat) -> LTE n (S n)
nLTESn Z = LTEZero
nLTESn (S k) = LTESucc (nLTESn k)

-- lemma that proves that if n is even, then half n is LTE n
halfnLTEn : (n: Nat) -> (pf : IsEven n) -> LTE (half n pf) n
halfnLTEn Z ZEven = LTEZero
halfnLTEn (S (S k)) (SSEven k p) =  lteTransitive (LTESucc (halfnLTEn k p)) (nLTESn (S k))

-- lemma that proves that if S n is even, then half S n is LTE n
halfSnLTEn : (n : Nat) -> (pf : IsEven (S n)) -> LTE (half (S n) pf) n
halfSnLTEn (S Z) (SSEven Z ZEven) = LTESucc LTEZero
halfSnLTEn (S (S k)) (SSEven (S k) pf) = lteTransitive (LTESucc (halfSnLTEn k pf)) (nLTESn (S k))

-- lemma that proves that if S n is even, then (n - 1)/2 is LTE n
halfnMinusoneLTEn : (n : Nat) -> (pf : IsEven (S n)) -> LTE (halfnMinusone n pf) n
halfnMinusoneLTEn (S Z) (SSEven Z ZEven) = LTEZero
halfnMinusoneLTEn (S (S k)) (SSEven (S k) pf) = lteTransitive (LTESucc (halfnMinusoneLTEn k pf)) (nLTESn (S k))

-- lemma that proves that if a = b, then a is LTE b
-- IMPORTANT : this is not Total
equalImpliesLTE : (a : Nat) -> (b : Nat) -> (a = b) -> LTE a b
equalImpliesLTE Z Z Refl = LTEZero
equalImpliesLTE (S k) (S k) Refl = LTESucc (equalImpliesLTE k k Refl)

-- proof that if n is even, then (n/2 + n/2) = n
nEqualhalfnplushalfn : (n : Nat) -> (pf : IsEven n) -> ((half n pf) + (half n pf)) = n
nEqualhalfnplushalfn Z ZEven = Refl
nEqualhalfnplushalfn (S (S k)) (SSEven k x) = rewrite (sym (plusSuccRightSucc (S (half k x)) (half k x))) in (cong {f = \l => (S (S l))} (nEqualhalfnplushalfn k x))

-- proof that if n is even, then n is LTE (n/2 + n/2)
nLTEhalfnplushalfn : (n : Nat) -> (pf : IsEven n) -> LTE n ((half n pf) + (half n pf))
nLTEhalfnplushalfn n pf = equalImpliesLTE n ((half n pf) + (half n pf)) (sym (nEqualhalfnplushalfn n pf))

-- proof that if S n is even, then ((n + 1)/2 + (n - 1)/2) = n
nEqualhalfOddn : (n : Nat) -> (pf : IsEven (S n)) -> ((half (S n) pf) + (halfnMinusone n pf)) = n
nEqualhalfOddn (S Z) (SSEven Z ZEven) = Refl
nEqualhalfOddn (S (S k)) (SSEven (S k) pf) = rewrite (sym (plusSuccRightSucc (S (half (S k) pf)) (halfnMinusone k pf))) in (cong {f = \l => (S (S l))} (nEqualhalfOddn k pf))

-- proof that if S n is even, then n is LTE ((n + 1)/2 + (n - 1)/2)
nLTEhalfOddn : (n : Nat) -> (pf : IsEven (S n)) -> LTE n ((half (S n) pf) + (halfnMinusone n pf))
nLTEhalfOddn n pf = equalImpliesLTE n ((half (S n) pf) + (halfnMinusone n pf)) (sym (nEqualhalfOddn n pf))

-- proof the n is either odd or even (done in class)
-- nOrSnEven: (n: Nat) -> Either (IsEven n) (IsEven (S n))
-- nOrSnEven Z = Left ZEven
-- nOrSnEven (S k) = case (nOrSnEven k) of
--                        (Left l) => Right (SSEven k l)
--                        (Right r) => Left r

-- function that takes a vector of even length, and divides it into two equal halves
halfVectEven : Vect n elem -> (pf : IsEven n) -> ((Vect (half n pf) elem), (Vect (half n pf) elem))
halfVectEven {n} xs pf = ((Vecttake (half n pf) xs (halfnLTEn n pf)), (Vecttakefromlast (half n pf) xs (halfnLTEn n pf)))

-- function that takes a vector of odd length, and divides it into two unequal parts ((n + 1)/2 and (n - 1)/2)
halfVectOdd : Vect n elem -> (pf : IsEven (S n)) -> ((Vect (half (S n) pf) elem), (Vect (halfnMinusone n pf) elem))
halfVectOdd {n} xs pf = ((Vecttake (half (S n) pf) xs (halfSnLTEn n pf)), (Vecttakefromlast (halfnMinusone n pf) xs (halfnMinusoneLTEn n pf)))

-- proof that n is LTE n (proved in class)
reflLTE : (n: Nat) -> LTE n n
reflLTE Z = LTEZero
reflLTE (S k) = LTESucc (reflLTE k)

-- lemma that a is LTE ((S a) + b)
lemma1 : (a : Nat) -> (b: Nat) -> LTE a ((S a) + b)
lemma1 Z b = LTEZero
lemma1 (S k) b = LTESucc (lemma1 k b)

-- lemma that (S (a + b)) is LTE (a + S b)
lemma2 : (a : Nat) -> (b : Nat) -> LTE (S (a + b)) (a + (S b))
lemma2 Z b = reflLTE (S b)
lemma2 (S k) b = LTESucc (lemma2 k b)

-- lemma that (S b) is LTE ((S a) + b)
lemma3 : (a : Nat) -> (b : Nat) -> LTE (S b) ((S a) + b)
lemma3 a Z = LTESucc LTEZero
lemma3 a (S k) = lteTransitive (LTESucc (lemma3 a k)) (lemma2 (S a) k)

--these are functions to cast a vector from one type to another
sillycast: (Vect ((S k) + j) elem) ->( Vect (k+ (S j)) elem)
sillycast {k} {j} v1 = (Vecttake k v1 (lemma1 k j)) ++ (Vecttakefromlast (S j) v1 (lemma3 k j))

sillycastEven : (n : Nat) -> (pf : IsEven n) -> (Vect ((half n pf) + (half n pf)) elem) -> Vect n elem
sillycastEven n pf xs = Vecttake n xs (nLTEhalfnplushalfn n pf)

sillycastOdd : (n : Nat) -> (pf : IsEven (S n)) -> (Vect ((half (S n) pf) + (halfnMinusone n pf)) elem) -> Vect n elem
sillycastOdd n pf xs = Vecttake n xs (nLTEhalfOddn n pf)

--The merge function
merge1 :Ord elem =>Vect  n elem ->Vect  m elem ->Vect (n+m) elem
merge1 [] ys = ys
merge1  (x :: xs) [] =  (x::xs)++[]
merge1 {n= (S k)}{m= (S j)} (x :: xs) (y :: ys) = case x<=y of
                                 False => y::(sillycast( (merge1  (x::xs) ys)))
                                 True => x::(merge1 xs (y::ys))

mergeNat : (v1 : (NatVect n)) -> (v2 : (NatVect m)) -> (NatVect (n + m))
mergeNat v1 v2 = merge1 v1 v2

--The mergesort function
-- working of mergesort :
-- Step 1 : Checks if the lenght of the vector is odd or Even
-- Step 2 : if Even -> split into two equal parts (n/2 , n/2 )
--          if Odd -> split into two unequal parts ( (n + 1)/2 , (n - 1)/2)
-- Step 3 : apply mergesort recursively on the two parts
-- Step 4 : merge the two sorted parts according to the merge1 function
-- Step 5 : The vector obtained from merge will be of the type Vect (a + b) elem,
--  where (a + b) = n. The Vector is cast into the type Vect n elem by the
--  sillycast functions.
mergesort :Ord elem => Vect n elem -> Vect n elem
mergesort [] = []
mergesort [x] = [x]
mergesort {n} xs = case (nOrSnEven n) of
                    (Left nEven) => sillycastEven n nEven (merge1 (mergesort (fst(halfVectEven xs nEven))) (mergesort (snd(halfVectEven xs nEven))))
                    (Right snEven) => sillycastOdd n snEven (merge1 (mergesort (fst(halfVectOdd xs snEven))) (mergesort (snd(halfVectOdd xs snEven))))

--GOAL : To prove that mergesort v is sorted for all vectors v with elem = Nat

-- Given a sorted vector (call it v) and an element (call it x) that is LTE the first element of v, proof that (x :: v) is sorted
total
addElemSorted : (x : Nat) -> (v : NatVect (S k)) -> (LTE x (Vect.index (FZ) v)) -> IsSorted (S k) v -> IsSorted (S (S k)) (x :: v)
addElemSorted x v pf1 pf2 FZ = reflLTE (Vect.index (FZ) (x :: v))
addElemSorted x v pf1 pf2 (FS FZ) = pf1
addElemSorted x v pf1 pf2 (FS (FS j)) = (pf2 (FS j))

-- mergeNatIsSorted : (v1 : Vect n Nat) -> (IsSorted n v1) -> (v2 : Vect m Nat) -> (IsSorted m v2) -> IsSorted (n + m) (mergeNat v1 v2)
-- mergeNatIsSorted {n = (S k)} {m = (S j)} (z :: xs) x (w :: ys) y = case (isLTE z w) of
--                                                                   (Yes pf) => addElemSorted z (mergeNat xs (w :: ys)) pf (mergeNatIsSorted xs x (w :: ys) y)
--                                                                   (No contra) => ?rhs
