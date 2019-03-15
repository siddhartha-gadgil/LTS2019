module Matrix

import Data.Vect
import fn_to_vect

%access public export

ZeroRow : (n : Nat) -> (typ : Type) -> (zero : typ) -> Vect n typ
ZeroRow Z typ zero = []
ZeroRow (S n) typ zero = zero::(ZeroRow n typ zero)

total
ZeroMat : (n : Nat) -> (m : Nat) -> (typ : Type) -> (zero : typ) -> Vect n (Vect m typ)
ZeroMat Z m typ zero = []
ZeroMat (S n) m typ zero = (ZeroRow m typ zero) :: (ZeroMat n m typ zero)

total
innerPdt : (n : Nat) -> (typ : Type) -> ((*) : typ -> typ -> typ) ->
           ((+) : typ -> typ -> typ) -> (zero : typ) ->
           Vect n typ -> Vect n typ -> typ

innerPdt Z typ (*) (+) zero [] [] = zero
innerPdt (S k) typ (*) (+) zero (x::xs) (y::ys) =
    x*y + (innerPdt k typ (*) (+) zero xs ys)

total
mulVect : (m : Nat) -> (k : Nat) -> (typ : Type) ->
          ((*) : typ -> typ -> typ) ->
          ((+) : typ -> typ -> typ) -> (zero : typ) ->
          Vect m typ -> Vect m (Vect k typ) -> Vect k typ

mulVect m k typ (*) (+) zero x ys = map (innerPdt m typ (*) (+) zero x) (transpose ys)

mulMat : (n : Nat) -> (m : Nat) -> (k : Nat) -> (typ : Type) ->
         ((*) : typ -> typ -> typ) -> ((+) : typ -> typ -> typ) -> (zero : typ) ->
         Vect n (Vect m typ) -> Vect m (Vect k typ) -> Vect n (Vect k typ)

mulMat Z m k typ (*) (+) zero [] xs = []
mulMat (S n) m k typ (*) (+) zero (x::xs) ys =
    (mulVect m k typ (*) (+) zero x ys)::(mulMat n m k typ (*) (+) zero xs ys)

Identity_Bool : (n : Nat) -> (Mat_Vect n n Bool)
Identity_Bool n = Diag_Mat_Vect n Bool False True

addMat : (n : Nat) -> (m : Nat) -> (ty : Type) ->
         ((+) : ty -> ty -> ty) -> (Mat_Vect n m ty) ->
         (Mat_Vect n m ty) -> (Mat_Vect n m ty)
addMat n m ty (+) u v = (Mat_fn_to_Vect n m ty fn) where
    fn_u : Mat_fn n m ty
    fn_u = Mat_Vect_to_fn n m ty u

    fn_v : Mat_fn n m ty
    fn_v = Mat_Vect_to_fn n m ty v

    fn : Mat_fn n m ty
    fn i j = (fn_u i j) + (fn_v i j)
