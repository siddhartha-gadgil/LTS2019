module VectPerm

import Data.Vect

-- Auxillary functions

Pred: Nat -> Nat
Pred Z = Z
Pred (S k) = k

-- same as Data.Vect.index, but a shorter name

Index : Fin len -> Vect len elem -> elem
Index FZ     (x::xs) = x
Index (FS k) (x::xs) = index k xs

-- nearly the same as Chinmaya's 'tofinNat', but this is total because I used modnatNZ instead of Eucl

intoFin : (a: Nat) -> (n : Nat) -> (Fin n)
intoFin Z Z = ?intoFin_rhs_3
intoFin Z (S k) = FZ
intoFin (S k) Z = ?intoFin_rhs_1
intoFin (S k) (S j) = case (isLTE (S k) (S j)) of
                           (Yes prf) => FS (intoFin k j)
                           (No contra) => assert_total (intoFin (modNatNZ (S k) (S j) SIsNotZ) (S j))

-- returns the element at position n in a vector (indexing starts with 0 as usual, as we are using Fin)

nPos: (a: Nat) -> (n: Nat) -> (x: Vect n Nat) -> Nat
nPos a n x = Index (intoFin a n) x

-- The function below is a helper function to show where (with proof) an element occurs in a vector
-- This will be useful for checking (with proof) if a Vector is a permutation of another.

improveElem: (n: Nat) -> (iter: Nat) -> (x: Vect n Nat) -> (find: Nat) -> (List (k: Nat ** (nPos k n x) = find))
improveElem n Z x find = case (decEq (nPos Z n x) find) of
                               (Yes Refl) => [(Z** Refl)]
                               (No contra) => []
improveElem n (S k) x find = case (decEq (nPos (S k) n x) find) of
                                   (Yes prf) => [((S k) ** prf)] ++ (improveElem n k x find)
                                   (No contra) => (improveElem n k x find)

-- finds all the occurences of the element 'find' in the vector 'x' with proof for each occurrence

findIn: (x: Vect n Nat) -> (find: Nat) -> (List (k: Nat ** (nPos k n x) = find))
findIn {n} x find = (improveElem n (Pred n) x find)

-- Next step: take an element from a list, take a proof that it occurs at position 'k', get the resultant list
-- by deleting the element from the position k

-- This can be used to check whether one vector is a permutation of another.
