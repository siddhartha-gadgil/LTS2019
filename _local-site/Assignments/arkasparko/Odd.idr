module arkaghosh.Odds

import Evens

import Intro

||| inductive type family IsOdd (Ques 1)
data IsOdd : Nat -> Type where
    SZOdd : IsOdd (S Z)
    SSOdd : (n : Nat) -> (IsOdd n) -> (IsOdd (S (S n))) 
    
||| witness that 3 is odd (Ques 2)   
threeOddProof : IsOdd 3
threeOddProof = SSOdd 1 SZOdd	

||| witness that 2 is not odd (Ques 3)
total
twoNotOdd : (IsOdd 2) -> Void
twoNotOdd SZOdd impossible -- twoNotOdd will be total even without this line
twoNotOdd (SSOdd Z pf) impossible

||| Property 1 - If n is odd then (S n) is even (Ques 4)
total
prop1 : (n : Nat) -> (IsOdd n) -> (IsEven (S n))
prop1 (S Z) SZOdd = SSEven Z ZEven
prop1 (S (S n)) (SSOdd n pf) = SSEven (S n) (prop1 n pf)

||| Property 2 - If n is even then (S n) is odd (Ques 5)
total
prop2 : (n : Nat) -> (IsEven n) -> (IsOdd (S n))
prop2 Z ZEven = SZOdd
prop2 (S (S n)) (SSEven n pf) = SSOdd (S n) (prop2 n pf)

||| Property 3 -  No number is both even and odd (Ques 7)
total
prop3 : (n : Nat) -> (IsOdd n) -> (IsEven n) -> Void
prop3 Z pf ZEven impossible
prop3 (S Z) SZOdd pf impossible
prop3 (S (S n)) (SSOdd n pf1) (SSEven n pf2) = prop3 n pf1 pf2 

||| Property 4 - If n and m are odd, then (n + m) is even (Ques 8)
total
prop4 : (n : Nat) -> (m : Nat) -> (IsOdd n) -> (IsOdd m) -> (IsEven (add n m))
prop4 Z m pf1 pf2 impossible
prop4 (S Z) m pf1 pf2 = prop1 m pf2
prop4 (S (S n)) m (SSOdd n pf1) pf2 = SSEven (add n m) (prop4 n m pf1 pf2)

||| Property 5 -  Every number n : Nat is either even or odd (Ques 6)
total
prop5 : (n : Nat) -> Either (IsEven n) (IsOdd n)
prop5 Z = Left ZEven
prop5 (S n) = f n  (prop5 n)
    where f : (m : Nat) -> (Either (IsEven m) (IsOdd m)) -> (Either (IsEven (S m)) (IsOdd (S m)))
          f m (Left pf) = Right (prop2 m pf)
          f m (Right pf) = Left (prop1 m pf)
          
||| Congruence : If n = m then f(n) = f(m)
total
congruence : (a : Type) -> (f : a -> a) -> (n : a) -> (m : a) -> (n = m) -> (f(n) = f(m))          
congruence typ f n n Refl = Refl          
          
          
||| Property 6 - if n is odd, then there exists m such that n = 2m + 1 (Ques 9)
total 
prop6 : (n : Nat) -> (IsOdd n) -> ( k: Nat ** S(double k) = n )
prop6 (S Z) SZOdd = (Z ** Refl)
prop6 (S (S n)) (SSOdd n pf) = ( (S m) ** pf1)
    where m : Nat
          pf2 : S(double m) = n
          m = fst(prop6 n pf)
          pf2 = snd(prop6 n pf)
          pf1 : S(double (S m)) = (S (S n))
          pf1 = congruence Nat f (S(double m)) n pf2
              where f : Nat -> Nat
                    f x = S( S x)
          
          
          




















 
