module AssRecRule

import Data.Fin
import Data.Vect

%default total

||| The recursion function for lists of type `a`. Define this by pattern matching

recList : (a : Type) ->  (x : Type) -> x -> (a -> List a -> x -> x) -> (List a -> x)

recList ty1 ty2 elem fun Nil = elem
recList ty1 ty2 elem fun (x :: xs) = (fun x xs (recList ty1 ty2 elem fun xs))

-------------------------------------------------------------------------------------------------------------------

||| Given a list of type `a` and a function `f: a -> b` get a list of type `b` by applying `f` to each element.
||| Note: Define using `recList` and without pattern matching on lists.

mapList : (a : Type) -> (b : Type) -> (f : a -> b) -> List a -> List b

mapList ty1 ty2 f = recList ty1 (List ty2) Nil fun where

    fun : ty1 -> (List ty1) -> (List ty2) -> (List ty2)
    fun x xs ys = (f x) :: ys

--------------------------------------------------------------------------------------------------------------------

||| Given a list of type `a`, an initial value `init : a` and an operation `op: a -> a -> a`,
||| get an element of `a` by starting with init and repeatedly applying the elements of the list.
||| e.g. fold Nat 1 (*) ([22] :: [3] :: [])  = 1 * 22 * 3
||| Note: Define using `recList` and without pattern matching on lists.

foldList : (a : Type) ->  (init : a) -> (op : a -> a -> a) -> List a -> a

foldList ty init op = recList ty ty init fun where
    fun : ty -> (List ty) -> ty -> ty
    fun x xs y = (op x y) -- it can be defined as (op y x) also depending on the need

--------------------------------------------------------------------------------------------------------------------

||| The induction function on the `Fin` indexed type family.
||| Define this by pattern matching.

inducFin : (xs : (n: Nat) -> Fin n -> Type) ->
  (base : (m: Nat) -> xs (S m) FZ) ->
  (step : (p: Nat) -> (k: Fin p) ->  (prev: xs p k) -> (xs (S p) (FS k))) ->
  (q: Nat) -> (j: Fin q) -> xs q j

inducFin xs base step Z k impossible
inducFin xs base step (S q) FZ = base q
inducFin xs base step (S Z) (FS k) impossible
inducFin xs base step (S (S q)) (FS k) = step (S q) k (inducFin xs base step (S q) k)

---------------------------------------------------------------------------------------------------------------------

||| Given a type `a`, a natural number `q`, an element `j : Fin q` and a vector `v` of length q with entries of type `a`,
||| get the element in position `j` of `v`. Note that this is always well defined.
||| Note: Define using `inducFin` and without pattern matching on the `Fin` family. You may pattern match on Vectors.

fetchElem : (a: Type) -> (q: Nat) -> (j: Fin q) -> (Vect q a -> a)

fetchElem ty q j = inducFin family base step q j where

    family : (n : Nat) -> (Fin n) -> Type
    family n k = (Vect n ty) -> ty

    base : (m : Nat) -> (family (S m) FZ)
    base m (x :: xs) = x

    step : (p : Nat) -> (k : Fin p) -> (prev : (family p k)) -> (family (S p) (FS k))
    step p k prev (x :: xs) = prev xs
