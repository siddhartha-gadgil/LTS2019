module Quicksort

import Data.Vect

total
partitionVect : Ord elem => (pivot : elem) -> (Vect n elem) -> (l1 : Nat ** l2 : Nat ** (Vect l1 elem, Vect l2 elem, n = (l1 + l2)))
partitionVect pivot [] = (0 ** 0 ** ([], [],Refl))
partitionVect pivot (x :: xs) with (partitionVect pivot xs)
  partitionVect pivot (x :: xs) | (l1 ** l2 ** ( v1, v2, equality)) = if (x <= pivot) then (S (l1) ** l2 ** ((x :: v1), v2, cong {f = S} equality)) else
    (l1 ** S (l2) ** (v1, x :: v2, trans (cong {f = S} equality) (plusSuccRightSucc l1 l2)))


-- qsort : Ord elem => Vect n elem -> (l1 ** l2 ** (Vect (l1 + l2) elem, (l1 + l2) = n))
