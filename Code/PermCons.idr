module permutation_with_constructors

import Data.Vect
import congruence

%access public export
%default total

--- Goal - To define permutations with constructors

data PermC : Nat -> Type where
    Idt : (n : Nat) -> PermC n -- Identity permutation
    Swap : (n : Nat) -> (pos : Fin n) -> (PermC n)
{-
    Flip : (n : Nat) -> PermC n -- [1 2 3 ... n]-> [2 1 3 ... n]
    Shift : (n : Nat) -> PermC n -- [1 2 3 .. n] -> [n 1 2 .. (n-1)]
-}
    CPerm : (n : Nat) -> PermC n -> PermC n -> PermC n

-----------------------------------------------------------------------------------------------------

||| Method to apply the permutation on a vector

applyPerm : (n : Nat) -> (typ : Type) -> (PermC n) -> (Vect n typ) -> (Vect n typ)

applyPerm Z typ perm v = v
applyPerm (S Z) typ perm v = v
applyPerm (S (S k)) typ (Idt (S (S k))) v = v

applyPerm (S (S k)) typ (Swap (S (S k)) FZ)  v =
    (index (FS FZ) v) :: ( (index FZ v) :: (tail(tail v)))

applyPerm (S (S k)) typ (Swap (S (S k)) (FS pos)) (a :: v) =
    a :: (applyPerm (S k) typ (Swap (S k) pos) v)
--applyPerm (S (S k)) t (Flip (S (S k))) v = (index (FS FZ) v) :: ( (index FZ v) :: (tail(tail v)))
--applyPerm (S (S k)) t (Shift (S (S k))) v = reverse( (index FZ v) :: (reverse (tail v)))

applyPerm n typ (CPerm n f g) v = applyPerm n typ f (applyPerm n typ g v)

-----------------------------------------------------------------------------------------------------

||| Proof that applyperm respects composition

applyPerm_Comp : (n : Nat) -> (typ : Type) -> (f, g : PermC n) -> (v : Vect n typ) ->
                 ( ((applyPerm n typ (CPerm n f g) ) v) = applyPerm n typ f (applyPerm n typ g v))

applyPerm_Comp Z typ p q v = Refl
applyPerm_Comp (S Z) typ p q v = Refl
applyPerm_Comp (S (S k)) typ p q v = Refl

{-
||| The permutation which shifts k times

many_shifts : (n : Nat) -> (k : Nat) -> (PermC n)
many_shifts n Z = Idt n
many_shifts n (S k) = CPerm n (Shift n) (many_shifts n k)
-}

-----------------------------------------------------------------------------------------------------

||| viewing a permutation of n elements as a permutation of (n + 1) elements with the first element
||| not moved

includePerm : (n : Nat) -> (PermC n) -> (PermC (S n))
includePerm Z perm = (Idt (S Z))
includePerm (S Z) perm = (Idt (S (S Z)))
includePerm n (Idt n) = Idt (S n)
includePerm n (Swap n pos) = Swap (S n) (FS pos)
--includePerm (S (S k)) (Flip (S (S k))) = Flip (S (S (S k)))
--includePerm (S (S k)) (Shift (S (S k))) = ?rhs
includePerm n (CPerm n f g) = CPerm (S n) (includePerm n f) (includePerm n g)

-----------------------------------------------------------------------------------------

appSwap : (n : Nat) -> (typ : Type) -> (k : Fin n) -> (Vect n typ) -> (Vect n typ)
appSwap n typ k v = applyPerm n typ (Swap n k) v

-----------------------------------------------------------------------------------------

||| auxilliary proof - a map from Fin Z to Void
aux_pf_1 : Fin Z -> Void
aux_pf_1 k impossible

-----------------------------------------------------------------------------------------

||| swap is the inverse of itself
Self_inv_swap : (n : Nat) -> (typ : Type) -> (k : (Fin n)) -> (v : (Vect n typ))->
                ((((appSwap n typ k) . (appSwap n typ k)) v) = v)

Self_inv_swap Z typ k v = Refl
Self_inv_swap (S Z) typ k v = Refl
Self_inv_swap (S (S n)) typ FZ (a :: b :: v) = Refl
Self_inv_swap (S (S n)) typ (FS k) (a :: v) =
     (rewrite (Self_inv_swap (S n) typ k v) in Refl)

------------------------------------------------------------------------------------------


Is_Left_Inv : (n : Nat) -> (typ : Type) -> (f : ((Vect n typ) -> (Vect n typ)) ) ->
              (g : ((Vect n typ) -> (Vect n typ)) ) -> Type
Is_Left_Inv n typ f g = ( (v : (Vect n typ)) -> ( ((g . f) v) = v))

------------------------------------------------------------------------------------------

Is_Right_Inv : (n : Nat) -> (typ : Type) -> (f : ((Vect n typ) -> (Vect n typ)) ) ->
               (g : ((Vect n typ) -> (Vect n typ)) ) -> Type
Is_Right_Inv n typ f g = ( (v : (Vect n typ)) -> ( ((f . g) v) = v))

------------------------------------------------------------------------------------------

Is_Inv : (n : Nat) -> (typ : Type) -> (f : ((Vect n typ) -> (Vect n typ)) ) ->
         (g : ((Vect n typ) -> (Vect n typ)) ) -> Type
Is_Inv n typ f g = ( (Is_Left_Inv n typ f g) , (Is_Right_Inv n typ f g))
------------------------------------------------------------------------------------------

||| (left) Inv(f.h) = (Inv h).(Inv f)

Left_Inv_comp : (n : Nat) -> (typ : Type) ->
                (f, g, h, k : ((Vect n typ) -> (Vect n typ)) ) ->
                (Is_Left_Inv n typ f g) -> (Is_Left_Inv n typ h k) ->
                (Is_Left_Inv n typ (f . h) (k . g))

Left_Inv_comp n typ f g h k pf_fg pf_hk = pf_3 where

    pf_1 : (v : (Vect n typ)) -> ((g (f (h v))) = (h v) )
    pf_1 v = pf_fg (h v)

    pf_2 : (v : (Vect n typ)) -> ( (k (g (f (h v)))) = (k (h v)) )
    pf_2 v = congruence (Vect n typ) (Vect n typ)
                        ((g . f . h) v) (h v) k (pf_1 v)

    pf_3 : (v : (Vect n typ)) -> ( (k (g (f (h v)))) = v )
    pf_3 v = trans (pf_2 v) (pf_hk v)

------------------------------------------------------------------------------------------

||| (right) Inv(f.h) = (Inv h).(Inv f)

Right_Inv_comp : (n : Nat) -> (typ : Type) ->
                 (f, g, h, k : ((Vect n typ) -> (Vect n typ)) ) ->
                 (Is_Right_Inv n typ f g) -> (Is_Right_Inv n typ h k) ->
                 (Is_Right_Inv n typ (f . h) (k . g))

Right_Inv_comp n typ f g h k pf_fg pf_hk = pf_3 where

   pf_1 : (v : (Vect n typ)) -> ((h (k (g v))) = (g v))
   pf_1 v = pf_hk (g v)

   pf_2 : (v : (Vect n typ)) -> ((f (h (k (g v)))) = (f (g v)) )
   pf_2 v = congruence (Vect n typ) (Vect n typ)
                       ((h . k . g) v) (g v) f (pf_1 v)

   pf_3 : (v : (Vect n typ)) -> ( (f (h (k (g v)))) = v)
   pf_3 v = trans (pf_2 v) (pf_fg v)

------------------------------------------------------------------------------------------


||| Inverse of f.g is (inv g).(inv f)

Inv_comp : (n : Nat) -> (typ : Type) ->
           (f, g, h, k : ((Vect n typ) -> (Vect n typ)) ) ->
           (Is_Inv n typ f g) -> (Is_Inv n typ h k) ->
           (Is_Inv n typ (f . h) (k . g))

Inv_comp n typ f g h k pf_fg pf_hk = let
    pf_left_fg = fst pf_fg
    pf_right_fg = snd pf_fg
    pf_left_hk = fst pf_hk
    pf_right_hk = snd pf_hk
    pf_left = Left_Inv_comp n typ f g h k pf_left_fg pf_left_hk
    pf_right = Right_Inv_comp n typ f g h k pf_right_fg pf_right_hk
    in
    (pf_left, pf_right)

------------------------------------------------------------------------------------------

||| The type of bijections

IsBijection : (n : Nat) -> (typ : Type) -> (f : (Vect n typ) -> (Vect n typ) ) -> Type
IsBijection n typ f =
    (g : ((Vect n typ) -> (Vect n typ)) ** ( Is_Inv n typ f g))


||| Proof that permutations are bijections


PermC_are_bij : (n : Nat) -> (typ : Type) -> (perm : PermC n) ->
                (IsBijection n typ (applyPerm n typ perm) )

PermC_are_bij Z typ perm = (idZ ** (fun, fun)) where
    idZ : (Vect Z typ) -> (Vect Z typ)
    idZ = applyPerm Z typ perm
    fun : (v : (Vect Z typ)) -> (v = v)
    fun v = Refl


PermC_are_bij (S Z) typ perm = (idSZ ** (fun, fun)) where
    idSZ : (Vect (S Z) typ) -> (Vect (S Z) typ)
    idSZ = applyPerm (S Z) typ (Idt (S Z))
    fun : (v : (Vect (S Z) typ)) -> (v = v)
    fun v = Refl

PermC_are_bij (S (S k)) typ (Idt (S (S k))) = (idn ** (fun, fun)) where
    idn : (Vect (S (S k)) typ) -> (Vect (S (S k)) typ)
    idn = applyPerm (S (S k)) typ (Idt (S (S k)))
    fun : (v : (Vect (S (S k)) typ)) -> (v = v)
    fun v = Refl


PermC_are_bij  (S (S k)) typ (Swap (S (S k)) pos) =
    ( (appSwap (S (S k)) typ pos) ** (fun, fun)) where
        fun : (v : Vect (S (S k)) typ ) ->
              ((((appSwap (S (S k)) typ pos) . (appSwap (S (S k)) typ pos)) v) = v)
        fun v = (Self_inv_swap (S (S k)) typ pos v)

PermC_are_bij n typ (CPerm n f h) = let
    inv_f = PermC_are_bij n typ f
    g = fst inv_f
    pf_fg = snd inv_f
    pf_fg_left = fst pf_fg
    pf_fg_right = snd pf_fg
    f1 = (applyPerm n typ f)

    inv_h = PermC_are_bij n typ h
    k = fst inv_h
    pf_hk = snd inv_h
    pf_hk_left = fst pf_hk
    pf_hk_right = snd pf_hk
    h1 = (applyPerm n typ h)

    pf_com = applyPerm_Comp n typ f h
    pf_com_1 = \v => (congruence (Vect n typ) (Vect n typ)
        (applyPerm n typ (CPerm n f h) v)
        (applyPerm n typ f (applyPerm n typ h v))
        (k . g) (pf_com v) )

    pf_left_1 =
        Left_Inv_comp n typ f1 g h1 k pf_fg_left pf_hk_left

    pf_left = \v => (trans (pf_com_1 v) (pf_left_1 v))

    pf_right_1 =
        Right_Inv_comp n typ f1 g h1 k pf_fg_right pf_hk_right

    pf_right = \v => (trans (pf_com ((k . g) v) ) (pf_right_1 v) )

    in
    ( (k . g) ** (pf_left , pf_right))
