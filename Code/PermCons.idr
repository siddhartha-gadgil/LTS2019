module permutation_with_constructors

import Data.Vect

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

{-
Is_Left_Inv : (n : Nat) -> (typ : Type) -> (f : ((Vect n typ) -> (Vect n typ)) ) -> 
              (g : ((Vect n typ) -> (Vect n typ)) ) -> Type
Is_Left_Inv n typ f = (g : ((Vect n typ) -> (Vect n typ)) ** 
                      ( (v : (Vect n typ)) -> ( ((g . f) v) = v)) )
-}                      
------------------------------------------------------------------------------------------                                  
{-
Is_Right_Inv : (n : Nat) -> (typ : Type) -> (f : ((Vect n typ) -> (Vect n typ)) ) -> Type
Is_Right_Inv n typ f = (g : ((Vect n typ) -> (Vect n typ)) ** 
                      ( (v : (Vect n typ)) -> ( ((f . g) v) = v)) )
                   
------------------------------------------------------------------------------------------

||| Left and right inverse implies inverse
Left_and_right_is_inv : (n : Nat) -> (typ : Type) -> (f                     
-}

------------------------------------------------------------------------------------------


||| Inverse of f.g is (inv g).(inv f)

||| define types Is_left_inverse, Is_right_inverse, Is_inverse.
||| define bijection in terms of these
||| define the above for left and right inverse separately 

------------------------------------------------------------------------------------------

||| The type of bijections

IsBijection : (n : Nat) -> (typ : Type) -> (f : (Vect n typ) -> (Vect n typ) ) -> Type
IsBijection n typ f = 
    (g : ((Vect n typ) -> (Vect n typ)) ** 
    ( (v : (Vect n typ)) -> ( (((g . f) v) = v) , (((f . g) v) = v) )))  

||| Proof that permutations are bijections

PermC_are_bij : (n : Nat) -> (typ : Type) -> (perm : PermC n) ->
                (IsBijection n typ (applyPerm n typ perm) )
                
PermC_are_bij Z typ perm = (idZ ** fun) where
    idZ : (Vect Z typ) -> (Vect Z typ)
    idZ = applyPerm Z typ perm
    fun : (v : (Vect Z typ)) -> ((v = v), (v = v))
    fun v = (Refl, Refl)  
    
PermC_are_bij (S Z) typ perm = (idSZ ** fun) where
    idSZ : (Vect (S Z) typ) -> (Vect (S Z) typ)
    idSZ = applyPerm (S Z) typ (Idt (S Z))
    fun : (v : (Vect (S Z) typ)) -> ((v = v), (v = v))
    fun v = (Refl, Refl)  
    
PermC_are_bij (S (S k)) typ (Idt (S (S k))) = (idn ** fun) where
    idn : (Vect (S (S k)) typ) -> (Vect (S (S k)) typ)
    idn = applyPerm (S (S k)) typ (Idt (S (S k)))
    fun : (v : (Vect (S (S k)) typ)) -> ((v = v), (v = v))
    fun v = (Refl, Refl)      
       
PermC_are_bij  (S (S k)) typ (Swap (S (S k)) pos) =
    ( (appSwap (S (S k)) typ pos) ** fun) where 
        fun : (v : Vect (S (S k)) typ ) -> 
              (((((appSwap (S (S k)) typ pos) . (appSwap (S (S k)) typ pos)) v) = v), 
               ((((appSwap (S (S k)) typ pos) . (appSwap (S (S k)) typ pos)) v) = v))
        fun v = ((Self_inv_swap (S (S k)) typ pos v), (Self_inv_swap (S (S k)) typ pos v)) 
        
PermC_are_bij n typ (CPerm n f g) = let
    inv_f = PermC_are_bij n typ f
    f1 = fst inv_f
    pf_f = snd inv_f -- (v : Vect n typ) -> (f1.f v) = v, (f.f1 v) = v) 
    
    inv_g = PermC_are_bij n typ g
    g1 = fst inv_g
    pf_g = snd inv_g -- (v : Vect n typ) -> (g1.g v) = v, (g.g1 v) = v)
    
    --fun : (v : (Vect n typ)) -> 
          --( (( g1 (f1 (applyPerm n typ (CPerm n f g) v))) = v), ( (applyPerm n typ (CPerm n f g) (g1 (f1 v))) = v) )
    --fun v = (?left v, ?right v)
    
    in
    ( (g1 . f1) ** ?fun)	   
   
   
   
   
   
   
    
    











