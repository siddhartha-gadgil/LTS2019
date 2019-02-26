module Graphs1
import Data.Vect

%access public export

{-This program works only for simple undirected graphs. and whenever I use "am" it means adjacency matrix.
Please give a symmetric matrix for am. The important functions in this program are
EdgeisPath
ConnectedComponents
PathWithProof
AdjacentsAreConnected
-}
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
|||A type inhabited if only if vertices i and j are connected by an edge
data Edge :(am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Type where
    Thereisanedge :(am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->(Accessnum am i j) =1 ->Edge am i j
|||A type inhabited iff vertices i and j are connected by a path
data Path : (am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)->Type where
  Self : (i:Nat)->Path am i i
  Adjacent : (Edge am i j) ->Path am i j
  Thereispath: (am:(Vect n (Vect n Nat)))-> (i:Nat)->(k:Nat) ->Path am i k->(Edge am j i)->Path am j k
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
|||Proves that adjacent vertices (ie vertices that have an edge between them are connected)
EdgeisPath :(am:(Vect n (Vect n Nat)))-> (Edge am i j)->Path am i j
EdgeisPath am (Thereisanedge am i j prf) = Adjacent (Thereisanedge am i j prf)


|||Checks whether a Natural number is in the list or not
isInList  : (i:Nat)->List Nat ->Bool
isInList i [] = False
isInList i (x :: xs) = case (x==i) of
                            False => isInList i xs
                            True => True
|||Updates an adjacency list if there is an edge between i and (S j) and calls the same function with j
adja :(am:(Vect n (Vect n Nat)))-> (i:Nat)->(j:Nat)  ->List (s:Nat**Path am i s)->List (s:Nat**Path am i s)
adja am i Z xs = xs
adja am i (S k) xs = case AdjacentsAreConnected am i (S k) of
                      Nothing => adja am i k xs
                      (Just x) => adja am i k (((S k )**x)::xs)
|||Returns a list of adjacent vectors to i with a proof that they are connected
Adjacents :(am:(Vect n (Vect n Nat)))-> (i:Nat)->List (s:Nat**Path am i s)
Adjacents {n} am i = adja am i n []
Adjacentlist:(am:(Vect n (Vect n Nat)))-> (i:Nat)->List Nat
Adjacentlist am i = map fst (Adjacents am i)
|||Returns the list of elements in the first list, but not in the second
Complement: List Nat ->List Nat ->List Nat
Complement [] ys = []
Complement (x :: xs) ys = case isInList x ys of
                               False => x::(Complement xs ys)
                               True => Complement xs ys



|||Does Depth first search of i and returns the list of elements connected to i
Dfs :(am:(Vect n (Vect n Nat)))-> (i:Nat) ->List Nat->List Nat
Dfs am i xs = case Complement (Adjacentlist am i) xs of
                     []=>xs
                     (j::ys)=>Dfs am i (Dfs am j (j::xs))

|||A helper function for ConnectedComponents
Connectedcompos: (am:(Vect n (Vect n Nat)))->List Nat ->List (List Nat)->(List (List Nat))
Connectedcompos{n} am xs ys = case Complement [1..n] xs of
                                [] => ys
                                (x :: zs) => Connectedcompos am (xs++(Dfs am x [x])) ((Dfs am x [x])::ys)

|||Gives the connected components of a graph as a list of lists
ConnectedComponents :  (am:(Vect n (Vect n Nat)))->(List (List Nat))
ConnectedComponents am = Connectedcompos am [] []



|||Modified depth first search which searches for a path between i and k. When there is no path, it behaves just like a depth first search from i
Dfss :(am:(Vect n (Vect n Nat)))-> (i:Nat) ->(k:Nat)->(Found:Bool)->List Nat->List Nat->((List Nat,List Nat),Bool)
Dfss am i k True path visit = ((path,visit),True)
Dfss am i k False path visit = case Complement (Adjacentlist am i) visit of
                     []=>(([],visit),False)
                     (j::ys)=>(case (k==j) of
                       True =>(((k::path),(j::visit)),True)
                       False =>  let dps =(Dfss am j k False (j::path) (j::visit)) in (let pathn = (case (snd(dps)) of
                                                                                             False => path
                                                                                             True => (fst (fst (dps)))) in (Dfss am i k  (snd(dps)) pathn (snd (fst (dps))))))


||| Ruturns a path between 2 vertices and returns Nothing if there is no path.
FindPath :(am:(Vect n (Vect n Nat)))->(k:Nat)->(i:Nat)->Maybe (List Nat)
FindPath am k i = case (k==i) of
                  True => Just [i]
                  False =>   (case isInList k (Dfs am  i [i])  of
                     False => Nothing
                     True => Just (fst (fst (Dfss am i k False [i] [i]))))
|||Gives the proof that there is a path between i and k when the path is not just one vertex long
Proofcon2 :(am:(Vect n (Vect n Nat)))-> List Nat -> (i:Nat)->(k:Nat)-> Path am i k
Proofcon2 am [j,p] i k = case checkEqNat p k of
                           (Just Refl) => (case AdjacentsAreConnected am i k of
                                                (Just x) => x)
Proofcon2 am (x::y::z::xs) i k =case AdjacentsAreConnected am i y of
                                                           (Just (Adjacent x)) => (let loop = Proofcon2 am (y::z::xs) y k in
                                                                 Thereispath am y k loop x )




|||Gives proof for 1 vertex long paths and calls proofcon2 when there are at least 2 vertices in the path
Proofcon :(am:(Vect n (Vect n Nat)))-> List Nat -> (i:Nat)->(k:Nat)-> Path am i k
Proofcon am xs i k = case checkEqNat i k of
                          (Just Refl) => Self i
                          Nothing => Proofcon2 am xs i k
|||Gives a path with proof when there is a path between k and i and Nothing when there is no path.
PathWithProof :(am:(Vect n (Vect n Nat)))->(k:Nat)->(i:Nat)->Maybe((List Nat),Path am k i )
PathWithProof am k i = case FindPath am k i of
                        Nothing => Nothing
                        Just x => Just (x,Proofcon am x k i)
