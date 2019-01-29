module permutation

import Data.Vect
import Data.Fin

%access public export

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
PermB : Nat -> Type
PermB n = ( f : F_Fin n ** ( g : F_Fin n ** ((a : (Fin n)) -> ((g (f a)) = a))))

||| Second definition of perm. I have strong feeling that using univalence this is equivalent
||| to the first definition.
total
Perm2 : Nat -> Type
Perm2 n = ( f : F_Fin n ** ( g : F_Fin n ** ((g . f) = (Idt (Fin n)))))

||| Nat to Fin
total
NatToFin : (k : Nat) -> (n : Nat) -> (pf : LTE (S k) n) -> (Fin n)
NatToFin k Z pf impossible
NatToFin Z (S n) pf = FZ
NatToFin (S k) (S n) (LTESucc pf) = FS (NatToFin k n pf)

||| applying a function on Finite sets on a vector
total
applyFun : (n : Nat)  -> (k : Nat) -> (v : NatVect n) -> 
           (f : F_Fin n) -> (pf : (LTE k n))
            -> (NatVect k)

applyFun n Z v f pf = []
applyFun n (S k) v f pf = reverse((Vect.index (f (NatToFin k n pf)) v) :: reverse((applyFun n k v f (prop k n pf)))) where
    prop : (a : Nat) -> (b : Nat) -> (LTE (S a) b) -> (LTE a b)
    prop Z b pf2 = LTEZero
    prop (S a) (S b) (LTESucc pf2) = LTESucc (prop a b pf2)
    




