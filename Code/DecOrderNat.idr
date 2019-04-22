module DecOrderNat

%access public export
%default total

||| The type of proof that between two elements one is less than
||| equal to another

data DecMin : (m , n : Nat) -> Type where
    Left : (LTE m n) -> DecMin m n
    Right : (LTE n m) -> DecMin m n

||| Decides which of the two numbers is smaller and gives the
||| proof along with the decision

decideSucc : (m , n : Nat) -> (DecMin m n) -> (DecMin (S m) (S n))
decideSucc m n (Left pf) = Left (LTESucc pf)
decideSucc m n (Right pf) = Right (LTESucc pf)

decMin : (m , n : Nat) -> (DecMin m n)
decMin Z n = Left LTEZero
decMin n Z = Right LTEZero
decMin (S m) (S n) = decideSucc m n (decMin m n)
