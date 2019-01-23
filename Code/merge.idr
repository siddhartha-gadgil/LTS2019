module Mergesort

import Data.Vect


Vecttake : (m:Nat)->Vect n elem->Vect m  elem
Vecttake Z xs = []
Vecttake (S k) (x::xs) = x::(Vecttake k xs)

Vecttakefromlast :(m:Nat)->Vect n elem ->Vect m elem
Vecttakefromlast m xs = reverse (Vecttake  m (reverse xs))






merge1 :Ord elem =>Vect  n elem ->Vect  m elem ->Vect (n+m) elem
merge1 [] ys = ys
merge1  (x :: xs) [] =  (x::xs)++[]
merge1 (x :: xs) (y :: ys) = case x<=y of
                                 False => y:: (merge1 xs (x::ys))
                                 True => x::(merge1 xs (y::ys))
{-

mergesort :Ord elem=>Vect n elem->Vect n elem
mergesort []=[]
mergesort [x] = [x]
mergesort {n} xs = (the (Vect n elem ) (merge left right)) where
  left = Vecttake s xs
  right = Vecttake (cast ((cast n)-(cast s))) xs where
    s =cast((cast n)/2)
    -}
