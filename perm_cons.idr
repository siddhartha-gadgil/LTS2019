module permutation_with_constructors

import Data.Vect

--- Goal - To define permutations with constructors

data Perm : Nat -> Type where
    Idt : (n : Nat) -> Perm n -- Identity permutation
    Flip : (n : Nat) -> Perm n -- [1 2 3 ... n]-> [2 1 3 ... n]
    Shift : (n : Nat) -> Perm n -- [1 2 3 .. n] -> [n 1 2 .. (n-1)]
    CPerm : (n : Nat) -> Perm n -> Perm n -> Perm n
    
total    
applyPerm : (n : Nat) -> (t : Type) -> (Perm n) -> (Vect n t) -> (Vect n t)
applyPerm Z typ p v = v
applyPerm (S Z) typ p v = v
applyPerm n typ (Idt n) v = v
applyPerm (S (S k)) t (Flip (S (S k))) v = (index (FS FZ) v) :: ( (index FZ v) :: (tail(tail v)))
applyPerm (S (S k)) t (Shift (S (S k))) v = reverse( (index FZ v) :: (reverse (tail v)))
applyPerm n t (CPerm n f g) v = applyPerm n t f (applyPerm n t g v)
