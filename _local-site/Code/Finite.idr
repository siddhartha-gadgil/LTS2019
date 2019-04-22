module Finite.idr

import Data.Fin

--- This is the module for the Finite sets

||| The Data type finite. It is the same as Fin except the size has been made explicit
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

