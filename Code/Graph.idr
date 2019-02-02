module Graphs

import Data.Vect

--This works only for simple graphs
|||Checks whether 2 numbers are equal and returns nothing or a proof of equality (From The Book by Edwin Brady)
checkEqNat: (num1:Nat)->(num2:Nat)->Maybe (num1=num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just x) => Just (cong x)
|||Returns the i j element of an m by n matrix and nothing if ij is out of bounds.
Access : Vect m (Vect n Nat)->(i:Nat)->(j:Nat)->Maybe Nat
Access {n}{m} xs i j = case ((integerToFin  ((cast j)-1) n),(integerToFin  ((cast i)-1) m)) of
                         (Nothing, _) => Nothing
                         (_ ,Nothing) => Nothing
                         (Just x, Just y) => Just ((Vect.index x (Vect.index y xs)))

|||Returns the i j element of an n by n matrix with 0 if it is out of bounds
Acces:Vect n (Vect n Nat)->(i:Nat)->(j:Nat)-> Nat
Acces xs i j = case Access xs i j of
                    Nothing => 0
                    (Just x) => x
|||A type inhabited if only if vertices i and j are connected
data Edge :(al:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Type where
    Thereisanedge :(al:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->(Acces al i j) =1 ->Edge al i j
|||A type inhabited iff vertices i and j are connected by a path
data Path : (al:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Type where
  Adjacent : (Edge al i j) ->Path al i j
  Thereispath: (al:(Vect n (Vect n Nat)))-> (i:Nat)->(k:Nat) ->Path al i k->(Edge al k j)->Path al i j
|||Returns Nothing if there is no edge or a proof that acces al i j =1
Isthereanedge: (al:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Maybe ( (Acces al i j ) = 1)
Isthereanedge al i j = case Access al i j of
                            Nothing => Nothing
                            (Just x) => (case checkEqNat (Acces al i j ) 1 of
                                              Nothing => Nothing
                                              (Just y) => (Just y))
|||Returns a proof that 2 adjacent vertices are connected or nothing if they are not connected.
AdjacentsAreConnected:(al:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Maybe (Path al i j)
AdjacentsAreConnected al i j = case Isthereanedge al i j of
                                    Nothing => Nothing
                                    (Just x) => Just (Adjacent (Thereisanedge al i j x))


Findpath :(al:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat) ->Maybe(List Nat,Path al i j)
Findpath al i j = ?Findpath_rhs
