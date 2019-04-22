module pigeonhole

-- a try to prove pegionhole principle

import Data.Fin
import Data.Vect

%access public export
%default total

same_hole : (n : Nat) -> (m : Nat) -> (Vect n (Fin m)) -> Type
same_hole n m v = (p : (Fin n) ** (q : (Fin n) ** 
                  ( prf : ((p = q) -> Void) ** ( (index p v) = (index q v)))))

---------------------------------------------------------------------------------------------------------------
                  
||| proof that Fin Z is empty                  
aux_prf_1 : (Fin Z) -> Void                  
aux_prf_1 q impossible

---------------------------------------------------------------------------------------------------------------

||| the type of proofs that a particular element is in the vector or not
data There_is : (n : Nat) -> (m : Nat) -> (v : Vect n (Fin m)) -> (a : Fin m) -> Type where
    Yes : (k : (Fin n) ** ( (index k v) = a)) -> (There_is n m v a)
    No : ( (k : (Fin n) ** ( (index k v) = a)) -> Void ) -> (There_is n m v a)

---------------------------------------------------------------------------------------------------------------

||| finds the first index with the given entry, or returns that there is no such index 
                 
is_there : (n : Nat) -> (m : Nat) -> (a : Fin m) -> (v : Vect n (Fin m)) -> 
           (There_is n m v a)

-- for vectors of length zero this is false clearly.                               
is_there Z m a v = No contra where 
    contra : ( (k : (Fin Z) ** ( (index k v) = a)) -> Void )
    contra = aux_prf_1 . fst

-- for vectors of non zero length it  checks if the first element is a.  
is_there (S n) m a (x :: v) = case (decEq x a) of

    -- If yes gives it as the proof
    Yes prf => Yes (FZ ** prf) 
                                
    -- if not then recursively checks the remaining part.
    No contra => (case (is_there n m a v) of   
                              
                      -- If the element is in the remaining part then gives the proof                       
                      Yes prf1 => (let       
                          k = fst prf1       
                          prf2 = snd prf1
                          in
                          ( Yes ( (FS k) ** prf2) ) )
                          
                      -- if the element is not in the remaining part recursively 
                      -- constructs the contradiction       
                      
                      No not_in_v => (No (\k => case  k of 
                                                (FZ ** prf3) => (contra prf3) -- 
                                                ((FS l) ** prf4) => (not_in_v (l ** prf4 ) )))) 
    
----------------------------------------------------------------------------------------------------------------
||| swaps two element in a vector
swap : (n : Nat) -> (m : Nat) -> (a, b : Fin m) -> (v : Vect n (Fin m)) -> (Vect n (Fin m))
swap Z _ _ _ _ = []
swap (S n) m a b (x :: v) = 
    case (decEq x a) of
        Yes prf => b :: (swap n m a b v)
        No prf => case (decEq x b) of
            Yes prf => a :: (swap n m a b v)
            No prf => x :: (swap n m a b v)                  
                  
----------------------------------------------------------------------------------------------------------------
                  
simple_case : (n : Nat) -> (v : Vect (S n) (Fin n) ) -> (same_hole (S n) n v)
simple_case Z v = void (aux_prf_1 (Vect.index FZ v ))
simple_case (S n) v = ?rhs


