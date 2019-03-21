module PermConsProperties


import Data.Vect
import congruence
import PermCons

%access public export
%default total

||| a :: (perm xs) = (includePerm perm) (a :: xs)

PermC_prp_1 : (n : Nat) -> (a : Nat) -> (xs : (Vect n Nat)) ->
              (perm : (PermC n)) -> 
              ( (a :: (applyPerm n Nat perm xs)) = 
                (applyPerm (S n) Nat (includePerm n perm) (a :: xs)))

PermC_prp_1 Z a Nil perm = Refl
PermC_prp_1 (S Z) a [x] perm = Refl
PermC_prp_1 (S (S k)) a xs (Idt (S (S k))) = Refl
PermC_prp_1 (S (S k)) a xs (Swap (S (S k)) FZ) = Refl
PermC_prp_1 (S (S k)) a xs (Swap (S (S k)) (FS l)) = Refl
PermC_prp_1 (S (S k)) a xs (CPerm (S (S k)) f g) = let
    
    f1 = applyPerm (S (S k)) Nat f 
    f2 = applyPerm (S (S (S k))) Nat (includePerm (S (S k)) f)
    g1 = applyPerm (S (S k)) Nat g 
    g2 = applyPerm (S (S (S k))) Nat (includePerm (S (S k)) g)
    
    pf1 = PermC_prp_1 (S (S k)) a xs g -- a :: (g1 xs) = (includePerm g1) (a :: xs)
    pf2 = congruence (Vect (S (S (S k))) Nat) (Vect (S (S (S k))) Nat)
        (a :: (g1 xs)) (g2 (a :: xs)) f2 pf1 -- f2 (a :: g1 xs) = f2 (g2 (a :: xs))
        
    v1 = g1 xs
    
    pf3 = PermC_prp_1 (S (S k)) a v1 f -- a :: (f1 v1) = f2 (a :: v1)   
    in
    (trans pf3 pf2)
    
PermC_prp_2 : (n : Nat) -> (u : (Vect n Nat)) -> ((applyPerm n Nat (Idt n) u) = u)
PermC_prp_2 Z u = Refl
PermC_prp_2 (S Z) u = Refl
PermC_prp_2 (S (S k)) u = Refl









	               
