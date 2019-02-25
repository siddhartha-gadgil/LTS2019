module sorting_with_proof

import Data.Vect
import Data.Fin
import Permutation
import PermCons
import Finite

%access public export

||| Type of proofs that a vector 'v' of length 'n' is sorted in increasing order.
||| It takes the following parameters : 'n'(length of the vector), 'v'(vector),
||| 'ind'(index). Check if v[ind - 1] <= v[ind]. Note that the predecessor
||| function takes care of the first index ( pred FZ = FZ ).
total
SortProof : (n : Nat) -> (NatVect n) -> (Fin n) -> Type
SortProof Z v a impossible
SortProof (S k) v l = LTE (Vect.index (pred l) v) (Vect.index l v)

||| If 'v' is a vector of length 'n' then an element of the Type
||| (IsSorted n v) is a function which given an index 'k' gives
||| a proof that v[k-1] <= v[k]. The special case for first
||| index is taken care of by the predecessor function
||| (pred FZ = FZ).
total
IsSorted : (n : Nat) -> (v : (NatVect n)) -> Type
IsSorted n v = (k : Fin n) -> (SortProof n v k)

||| An element of the type SortedVect n v is of the form (v_sorted, perm, pfPerm, pfSort)
||| where 'v_sorted' is 'v' with its element sorted in increasing order. 'perm' is a
||| permutation such that perm(v) = v_sorted. 'pfPerm' is a proof that perm(v) = v_sorted.
||| 'pfSort' is a proof that 'v_sorted' is sorted.
total
SortedVect : (n : Nat) -> (v : (NatVect n)) -> Type
SortedVect n v = (v_sorted : (NatVect n) **
                 (perm : (PermC n) ** (((applyPerm n Nat perm v) = v_sorted), (IsSorted n v))))
