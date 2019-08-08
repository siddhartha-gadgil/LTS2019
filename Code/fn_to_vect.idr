module fn_to_vect

import Data.Vect
import Data.Fin

%access public export
%default total
-- module to convert a function to a vectot and a vector to a
-- function

||| Converts a vector to the corresponding function
vect_to_fn : (n : Nat) -> (ty : Type)-> (Vect n ty) ->
             (k : Fin n) -> ty
vect_to_fn n ty v k = index k v

||| Converts a function to the reversed vector
fn_to_vect : (n : Nat) -> (ty : Type) -> ((k : Fin n) -> ty) ->
             (Vect n ty)
fn_to_vect Z ty fn = []
fn_to_vect (S k) ty fn = (fn FZ) ::
      (fn_to_vect k ty smaller) where
          smaller : ((l : Fin k) -> ty)
          smaller l = fn (FS l)
--
-- ||| Converts a function to the corresponding vector
-- fn_to_vect : (n : Nat) -> (ty : Type) -> ((k : Fin n) -> ty) ->
--              (Vect n ty)
-- fn_to_vect n ty fn = fn_to_vect_rev n ty fn
--   -- reverse (fn_to_vect_rev n ty fn)

||| Definition of Matrices using vectors
Mat_Vect : (n : Nat) -> (m : Nat) -> (ty : Type) -> Type
Mat_Vect n m ty = Vect n (Vect m ty)

||| Definition of Matrices using functions
Mat_fn : (n : Nat) -> (m : Nat) -> (ty : Type) -> Type
Mat_fn n m ty = (i : Fin n) -> (j : Fin m) -> ty

||| From a matrix to its corresponding function
Mat_Vect_to_fn : (n : Nat) -> (m : Nat) -> (ty : Type) ->
                 (Mat_Vect n m ty) -> (Mat_fn n m ty)

Mat_Vect_to_fn n m ty vec i j = index j (index i vec)

||| From a function to the corresponding vector
Mat_fn_to_Vect : (n : Nat) -> (m : Nat) -> (ty : Type) ->
                     (Mat_fn n m ty) -> (Mat_Vect n m ty)

Mat_fn_to_Vect Z m ty fn = []
Mat_fn_to_Vect (S n) m ty fn = (v_top :: v_down) where
  fn_top : ( Fin m ) -> ty
  fn_top j = fn FZ j
  v_top : Vect m ty
  v_top = fn_to_vect m ty fn_top
  fn_down : Mat_fn n m ty
  fn_down i j = fn (FS i) j
  v_down : Mat_Vect n m ty
  v_down = Mat_fn_to_Vect n m ty fn_down

Diag_Mat_fn : (n : Nat) -> (ty : Type) ->
              (zero : ty) -> (elem : ty) ->
              (Mat_fn n n ty)
Diag_Mat_fn n ty zero elem i j = case (decEq i j) of
      Yes prf => elem
      No cont => zero

Diag_Mat_Vect : (n : Nat) -> (ty : Type) ->
                (zero : ty) -> (elem : ty) ->
                (Mat_Vect n n ty)
Diag_Mat_Vect n ty zero elem =
      Mat_fn_to_Vect n n ty (Diag_Mat_fn n ty zero elem)

Id_Mat_Nat : (n : Nat) -> Mat_Vect n n Nat
Id_Mat_Nat n = Diag_Mat_Vect n Nat Z (S Z)
