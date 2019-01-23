module Mergesort

import Data.Vect

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



--this function is to cast a vector from one type to another
sillycast: (v1:(Vect ((S k) + j) elem)) ->( Vect (k+ (S j)) elem)
sillycast {k} {j} v1 = (Vecttake k v1) ++(Vecttakefromlast (S j) v1)
--The merge function
merge1 :Ord elem =>Vect  n elem ->Vect  m elem ->Vect (n+m) elem
merge1 [] ys = ys
merge1  (x :: xs) [] =  (x::xs)++[]
merge1 {n= (S k)}{m= (S j)} (x :: xs) (y :: ys) = case x<=y of
                                 False => y::(sillycast( (merge1  (x::xs) ys)))
                                 True => x::(merge1 xs (y::ys))




{-mergesort :Ord elem=>Vect n elem->Vect n elem
mergesort []=[]
mergesort [x] = [x]
mergesort {n} xs = (the (Vect n elem ) (merge left right)) where
  left = mergesort (Vecttake s xs)
  right = mergesort (Vecttake (cast ((cast n)-(cast s))) xs) where
    s =cast((cast n)/2)-}
