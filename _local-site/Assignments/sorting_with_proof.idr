module sorting_with_proof

import Data.Vect
import Data.Fin

||| Vectors of Natural numbers
total
NatVect : Nat -> Type 
NatVect n = Vect n Nat

||| The type Fin n -> Fin n
total
F_Fin : Nat -> Type
F_Fin n = (Fin n) -> (Fin n) 

||| Identity function
total
Idt : (t : Type) -> t -> t
Idt s a = a

||| The type of permutation/bijection of {1,...,n}. 
||| Notice that for finite sets one sided inverse is enough. 
||| Also I have a strong feeling that using univalence the last part of the definition is 
||| equivalent to saying that (g . f) and Idt are equivalent
total
Perm : Nat -> Type
Perm n = ( f : F_Fin n ** ( g : F_Fin n ** ((a : (Fin n)) -> ((g (f a)) = a))))

||| Second definition of perm. I have strong feeling that using univalence this is equivalent
||| to the first definition.
total
Perm2 : Nat -> Type
Perm2 n = ( f : F_Fin n ** ( g : F_Fin n ** ((g . f) = (Idt (Fin n)))))

data Finite : Nat -> Type where
    FinZ : (k : Nat) -> (Finite (S k))
    FinS : (k : Nat) -> (Finite k) -> (Finite (S k)) 

total
Finite_to_Fin : (k : Nat) -> (Finite k) -> (Fin k)
Finite_to_Fin Z a impossible
Finite_to_Fin (S k) (FinZ k) = FZ
Finite_to_Fin (S k) (FinS k nm) = FS (Finite_to_Fin k nm) 

total 
Fin_to_Finite : (k : Nat) -> (Fin k) -> (Finite k)
Fin_to_Finite Z a impossible
Fin_to_Finite (S k) FZ = FinZ k
Fin_to_Finite (S k) (FS l) = FinS k (Fin_to_Finite k l)

||| Predecessor function for finite
total
predFinite : (k : Nat) -> (Finite k) -> (Finite k)
predFinite Z a impossible
predFinite (S k) (FinZ k) = FinZ k
predFinite (S (S k)) (FinS (S k) (FinZ k)) = FinZ (S k)
predFinite (S (S k)) (FinS (S k) l) = FinS (S k) (predFinite (S k) l)

||| Predecessor function for fin
total
predFin : (n : Nat) -> (Fin n) -> (Fin n)
predFin n a = Finite_to_Fin n ( predFinite n (Fin_to_Finite n a))

||| Type of proofs that a vector is sorted in increasing order. 
||| Note that the predecessor function takes care of the first index 
total
SortProof : (n : Nat) -> (NatVect n) -> (Fin n) -> Type 
SortProof Z v a impossible
SortProof (S k) v l = LTE (Vect.index (pred l) v) (Vect.index l v)

||| Type of the sorted vectors.
SortedVect : Type
SortedVect = (n : Nat ** (v : (NatVect n)  ** ((k : Fin n) -> (SortProof n v k)))) 







