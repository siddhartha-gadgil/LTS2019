module Mergesort

import Data.Vect

import Lecture_Evens

--Takes the first m elements from a vector
Vecttake : (m:Nat)->Vect n elem->Vect m  elem
Vecttake Z xs = []
Vecttake (S k) (x::xs) = x::(Vecttake k xs)

--Takes the last m elements from a vector
Vecttakefromlast :(m:Nat)->Vect n elem ->Vect m elem
Vecttakefromlast m xs = reverse (Vecttake  m (reverse xs))


insertend : (x:elem)->Vect n elem->Vect (S n) elem
insertend x [] = [x]
insertend x (y :: xs) = y::(insertend x xs)

-- half : (n: Nat) -> IsEven n -> Nat
-- half Z ZEven = 0
-- half (S (S k)) (SSEven k x) = S (half k x)

-- nOrSnEven: (n: Nat) -> Either (IsEven n) (IsEven (S n))
-- nOrSnEven Z = Left ZEven
-- nOrSnEven (S k) = case (nOrSnEven k) of
--                        (Left l) => Right (SSEven k l)
--                        (Right r) => Left r

--Defined in class. This is used to split the input vector into two parts.
--The length of the first part is halfRoof n.
-- halfRoof: Nat -> Nat
-- halfRoof n = case (nOrSnEven n) of
--                   (Left nEven) => half n nEven
--                   (Right snEven) => half (S n) snEven

--function that returns (n - halfRoof n) i.e. the length of the second part
--after input vector is split.
halfRoofComplement : Nat -> Nat
halfRoofComplement Z = Z
halfRoofComplement (S k) = halfRoof k

--function that splits a vector into two parts at its mid point.
--if n is even, it gives two halves of length n/2 each.
--if n is odd, the first half is (n+1)/2 length and the second half is
--(n-1)/2 length
halfVect : Vect n elem -> ((Vect (halfRoof n) elem), (Vect (halfRoofComplement n) elem))
halfVect {n} xs = ((Vecttake (halfRoof n) xs), (Vecttakefromlast (halfRoofComplement n) xs))

--this function is to cast a vector from one type to another
sillycast: (v1:(Vect ((S k) + j) elem)) ->( Vect (k+ (S j)) elem)
sillycast {k} {j} v1 = (Vecttake k v1) ++ (Vecttakefromlast (S j) v1)

--function to cast a vector from one type to another.
--makes the vector obtained on applying merge to two halves same as
--the type of the input vector.
sillycast2 : (Vect ((halfRoof n) + (halfRoofComplement n)) elem) -> Vect n elem
sillycast2 {n} xs = Vecttake n xs

--The merge function
merge1 :Ord elem =>Vect  n elem ->Vect  m elem ->Vect (n+m) elem
merge1 [] ys = ys
merge1  (x :: xs) [] =  (x::xs)++[]
merge1 {n= (S k)}{m= (S j)} (x :: xs) (y :: ys) = case x<=y of
                                 False => y::(sillycast( (merge1  (x::xs) ys)))
                                 True => x::(merge1 xs (y::ys))

--The mergesort function
mergesort :Ord elem => Vect n elem -> Vect n elem
mergesort [] = []
mergesort [x] = [x]
mergesort xs = sillycast2 (merge1 (mergesort (fst(halfVect xs))) (mergesort (snd(halfVect xs))))
