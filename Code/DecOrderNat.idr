module DecOrderNat

%access public export
%default total

||| The type of proof that between two elements one is less than 
||| equal to another

data DecMin : (m , n : Nat) -> Type where
    left : (LTE m n) -> DecMin m n
    right : (LTE n m) -> DecMin m n
    
||| Decides which of the two numbers is smaller and gives the
||| proof along with the decision
    
decideSucc : (m , n : Nat) -> (DecMin m n) -> (DecMin (S m) (S n))
decideSucc m n (left pf) = left (LTESucc pf)
decideSucc m n (right pf) = right (LTESucc pf)    
    
decMin : (m , n : Nat) -> (DecMin m n)
decMin Z n = left LTEZero
decMin n Z = right LTEZero
decMin (S m) (S n) = decideSucc m n (decMin m n)

