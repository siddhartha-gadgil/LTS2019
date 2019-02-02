module Graphs

import Data.Vect

--This works only for simple undirected graphs. and whenever I use "am" it means adjacency matrix. Please give a symmetric matrix for am
|||Checks whether 2 numbers are equal and returns nothing or a proof of equality
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
Accessnum:Vect n (Vect n Nat)->(i:Nat)->(j:Nat)-> Nat
Accessnum xs i j = case Access xs i j of
                    Nothing => 0
                    (Just x) => x
|||A type inhabited if only if vertices i and j are connected
data Edge :(am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Type where
    Thereisanedge :(am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->(Accessnum am i j) =1 ->Edge am i j
|||A type inhabited iff vertices i and j are connected by a path
data Path : (am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Type where
  Adjacent : (Edge am i j) ->Path am i j
  Thereispath: (am:(Vect n (Vect n Nat)))-> (i:Nat)->(k:Nat) ->Path am i k->(Edge am k j)->Path am i j
|||Returns Nothing if there is no edge or a proof that Accessnum am i j =1
Isthereanedge: (am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Maybe ( (Accessnum am i j ) = 1)
Isthereanedge am i j = case Access am i j of
                            Nothing => Nothing
                            (Just x) => (case checkEqNat (Accessnum am i j ) 1 of
                                              Nothing => Nothing
                                              (Just y) => (Just y))
|||Returns a proof that 2 adjacent vertices are connected or nothing if they are not connected.
AdjacentsAreConnected:(am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Maybe (Path am i j)
AdjacentsAreConnected am i j = case Isthereanedge am i j of
                                    Nothing => Nothing
                                    (Just x) => Just (Adjacent (Thereisanedge am i j x))
{-

Findpath :(am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat) ->Maybe(List Nat,Path am i j)
Findpath am i j = ?Findpath_rhs
-}
