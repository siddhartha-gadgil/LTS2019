module InsertionHelpers

import Data.Vect
import congruence
import Data.Fin
import Permutation
import PermCons
import Finite
-- import DecOrderNat
import LTE_Properties
import SortingWithProof
import InsertionSort

%access public export
%default total

||| Proof that one element list is always sorted

insertHelper8 : (y : Nat) -> (IsSorted (S Z) [y])
insertHelper8 y FZ = LTE_Property1 y

||| x :: xs is sorted . a < x . a :: x :: xs is sorted

insertHelper1 : (n : Nat) -> (a, x : Nat) ->
                (xs : (Vect n Nat)) -> (LTE a x) ->
                (IsSorted (S n) (x :: xs) ) ->
                (IsSorted (S (S n)) (a :: x :: xs) )

insertHelper1 Z a x Nil pfLTE pfSort FZ = (LTE_Property1 a)
insertHelper1 Z a x Nil pfLTE pfSort (FS FZ) = pfLTE
insertHelper1 (S k) a x xs pfLTE pfSort FZ = (LTE_Property1 a)
insertHelper1 (S k) a x xs pfLTE pfSort (FS FZ) = pfLTE
insertHelper1 (S k) a x xs pfLTE pfSort (FS (FS l)) =
    pfSort (FS l)

insertHelper9 : (k : Nat) -> (x : Nat) -> (xs : Vect k Nat) ->
                (IsSorted (S k) (x :: xs)) ->
                (IsSorted k xs)

insertHelper9 (S k) x xs pfSort FZ = LTE_Property1 (index FZ xs)
insertHelper9 (S k) x xs pfSort (FS l) = pfSort (FS (FS l))

vect_prp1 : (n : Nat) -> (xs : (Vect (S n) Nat)) ->
             (xs = ((head xs) :: (tail xs)))

vect_prp1 Z (a :: Nil) = Refl
vect_prp1 (S n) (a :: xs) = Refl

insertHelper10 : (n : Nat) -> (xs : (Vect (S n) Nat)) ->
                 (k : Fin (S n)) -> (LTE (index (pred k) xs) (index k xs)) ->
                 (LTE (index (pred k) ((head xs) :: (tail xs))) (index k ((head xs) :: (tail xs))))

insertHelper10 n (y :: ys) k pf = pf

transport : (typ : Type) -> (a, b : typ) -> (P : (typ -> Type)) -> (a = b) -> (P a) -> (P b)
transport typ a a P Refl pf = pf

insertHelper11 : (n : Nat) -> (u, v : (Vect (S n) Nat)) -> (u = v) -> (IsSorted (S n) u) ->
                (IsSorted (S n) v)

insertHelper11 n u v pfEq sort_pf k = let

    pf1 = congruence (Vect (S n) Nat) Nat u v (index (pred k)) pfEq -- u[k-1] = v[k-1]
    pf2 = congruence (Vect (S n) Nat) Nat u v (index k) pfEq -- u[k] = v[k]
    pf3 = sort_pf k -- u[k - 1] < u[k]
    u_k1 = index (pred k) u
    u_k = index k u
    v_k1 = index (pred k) v
    v_k = index k v
    pf4 = transport Nat u_k v_k (LTE u_k1) pf2 pf3 -- u_k1 < v_k
    pf5 = transport Nat u_k1 v_k1 (\l => LTE l v_k) pf1 pf4

    in
    pf5

--vect_prp_2 : (n : Nat) -> (v : (Vect (S n) Nat)) -> (index

----------------------------------------------------------------------------------------------------------------

insertHelper3 : (a : Nat) -> (x : Nat) -> (LTE x a) ->
                (IsSorted (S (S Z)) (x :: [a]) )

insertHelper3 a x pfLTE FZ = LTE_Property1 x
insertHelper3 a x pfLTE (FS FZ) = pfLTE

----------------------------------------------------------------------------------------------------------------

insertHelper12 : (n : Nat) -> (ys : (Vect (S n) Nat)) -> ((index FZ ys) = (head ys))
insertHelper12 n (y :: ys) = Refl

----------------------------------------------------------------------------------------------------------------

insertHelper13 : (n : Nat) -> (y : Nat) -> (ys : (Vect n Nat)) -> ( (tail (y :: ys)) = ys)
insertHelper13 n y ys = Refl
