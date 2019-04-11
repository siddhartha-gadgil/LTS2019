module VectPerm


import Data.Vect

%default total

-- Auxillary functions

Nats: Type
Nats = (Nat, Nat)

FST: (Vect k Nat, Vect k Nat) -> Vect k Nat
FST (a, b) = a

SND: (Vect k Nat, Vect k Nat) -> Vect k Nat
SND (a, b) = b

headL: (s: List Nat) -> (Not (s = [])) -> Nat
headL [] x = 0
headL (y :: xs) x = y

-- converting lists to vectors

makeVectList: (n: Nat) -> (Vect n Nat) -> (List Nat)
makeVectList Z [] = []
makeVectList (S len) (x :: xs) = [x] ++ (makeVectList len xs)

makeVectPairListPair: (Vect n Nat, Vect n Nat) -> (List Nat, List Nat)
makeVectPairListPair {n} (a, b) = (makeVectList n a, makeVectList n b)

makeListVect: (s: List Nat) -> (Vect (length s) Nat)
makeListVect s = (fromList s)

makeListPairVectPair: (a: (List Nat, List Nat)) -> (Vect (length (fst a)) Nat, Vect (length (snd a)) Nat)
makeListPairVectPair a = (makeListVect (fst a), makeListVect (snd a))

Pred: Nat -> Nat
Pred Z = Z
Pred (S k) = k

-- same as Data.Vect.index, but a shorter name

Index : Fin len -> Vect len elem -> elem
Index FZ     (x::xs) = x
Index (FS k) (x::xs) = index k xs

-- nearly the same as Chinmaya's 'tofinNat', but this is total because I used modnatNZ instead of Eucl

intoFin : (a: Nat) -> (n : Nat) -> (Fin n)
intoFin Z Z = ?intoFin_rhs_3
intoFin Z (S k) = FZ
intoFin (S k) Z = ?intoFin_rhs_1
intoFin (S k) (S j) = case (isLTE (S k) (S j)) of
                           (Yes prf) => FS (intoFin k j)
                           (No contra) => assert_total (intoFin (modNatNZ (S k) (S j) SIsNotZ) (S j))

-- returns the element at position n in a vector (indexing starts with 0 as usual, as we are using Fin)

nPos: (a: Nat) -> (n: Nat) -> (x: Vect n Nat) -> Nat
nPos a n x = Index (intoFin a n) x

replaceWithZ: (x: Vect n Nat) -> (pos: Nat) -> (Vect n Nat)
replaceWithZ {n} x pos = replaceAt (intoFin pos n) (Z) (x)

-- The function below is a helper function to show where (with proof) an element occurs in a vector
-- This will be useful for checking (with proof) if a Vector is a permutation of another.

improveElem: (n: Nat) -> (iter: Nat) -> (x: Vect n Nat) -> (find: Nat) -> (List (k: Nat ** (nPos k n x) = find))
improveElem n Z x find = case (decEq (nPos Z n x) find) of
                               (Yes Refl) => [(Z** Refl)]
                               (No contra) => []
improveElem n (S k) x find = case (decEq (nPos (S k) n x) find) of
                                   (Yes prf) => [((S k) ** prf)] ++ (improveElem n k x find)
                                   (No contra) => (improveElem n k x find)

-- finds all the occurences of the element 'find' in the vector 'x' with proof for each occurrence

findIn: (x: Vect n Nat) -> (find: Nat) -> (List (k: Nat ** (nPos k n x) = find))
findIn {n} x find = (improveElem n (Pred n) x find)

-- Next step: take an element from a list, take a proof that it occurs at position 'k', get the resultant list
-- by deleting the element from the position k

-- This can be used to check whether one vector is a permutation of another.

-- gives all occurences of x[pos] in y with proof

thisElemthatVect: (x: Vect n Nat) -> (pos: Nat) -> (y: Vect n Nat) -> (List (k: Nat ** (nPos k n y) = (nPos pos n x)))
thisElemthatVect {n} x pos y = findIn y (nPos pos n x)

-- given a vector x, it removes the element at position 'pos' (indexing from 0)

removeElem: (x: Vect (S n) Nat) -> (pos: Nat) -> (Vect n Nat)
removeElem {n} (x :: xs) Z = xs
removeElem {n=Z} (x :: xs) (S k) = []
removeElem {n=(S j)} (x :: xs) (S k) = [x] ++ (removeElem xs k)

-- checks if x[pos] occurs in y, and if it does, deletes them from the arrays

checkEqualElement: (x: Vect (S n) Nat) -> (y: Vect (S n) Nat) -> (pos: Nat) -> (k: Nat ** (nPos k (S n) y) = (nPos pos (S n) x)) -> (Vect n Nat, Vect n Nat)
checkEqualElement {n=Z} (x :: xs) (y :: ys) Z z = ([],[])
checkEqualElement {n=Z} [a] [b] (S k) z = ([], [])
checkEqualElement {n=(S k)} (x :: xs) (y :: ys) pos z = ( (removeElem (x::xs) pos), (removeElem (y::ys) (fst z)) )

removeIfequal: (x: Vect (S n) Nat) -> (y: Vect (S n) Nat) -> (pos: Nat) -> Either ((Vect (S n) Nat), (Vect (S n) Nat)) ((Vect n Nat), (Vect n Nat))
removeIfequal {n} x y pos = case (nonEmpty (thisElemthatVect x pos y)) of
                           (Yes prf) => Right (checkEqualElement x y pos (head (thisElemthatVect x pos y)))
                           (No contra) => Left (x, y)

-- recursively removes all the elements which occur in both x and y

removeRepeatedly: (iter: Nat) -> (x: Vect n Nat) -> (y: Vect n Nat) -> (List Nat, List Nat)
removeRepeatedly iter [] [] = ([], [])
removeRepeatedly Z (x :: xs) (y :: ys) = case (removeIfequal (x::xs) (y::ys) Z) of
                                              (Left l) => (makeVectPairListPair l)
                                              (Right r) => (makeVectPairListPair r)
removeRepeatedly (S k) (x :: xs) (y :: ys) = case (removeIfequal (x::xs) (y::ys) (S k)) of
                                                  (Left l) => (removeRepeatedly k (FST l) (SND l))
                                                  (Right r) => (removeRepeatedly k (FST r) (SND r))

-- produces the elements which occur in only one list and not another (symmetric difference of lists)

listDifference: (x: Vect n Nat) -> (y: Vect n Nat) -> (List Nat, List Nat)
listDifference {n} x y = removeRepeatedly (Pred n) x y

-- Two Boolean tests for permutations. The first one checks if the list difference is zero.

PermutationTest: (x: Vect n Nat) -> (y: Vect n Nat) -> Bool
PermutationTest x y = case (fst (listDifference x y)) of
                           [] => True
                           (x :: xs) => False

-- The second one works recursively. This will be more suited to turning into a proof.

recursiveTest: (x: Vect n Nat) -> (y: Vect n Nat) -> Bool
recursiveTest {n = Z} x y = True
recursiveTest {n= (S Z)} [a] [b] = case (decEq a b) of
                                        (Yes prf) => True
                                        (No contra) => False
recursiveTest {n = (S k)} x y = case (thisElemthatVect x Z y) of
                                     [] => False
                                     (head :: rest) => recursiveTest (removeElem x Z) (removeElem y (fst head))


-- Permutations as Bijections

-- This function is a helper function which checks each position of the Vector x and finds a corresponding element in y. Then, to make
-- sure nothing is repeated, it replaces the instance of x[pos] in y with Zero (please use positive elements in the vector). This was
-- required for constructing bijections between Vectors with repeated elements; there is a simpler way to do it in case the elements
-- are not repeated.

reversedBiject: (x: Vect n Nat) -> (y: Vect n Nat) -> (xpos: Nat) -> (List Nat)
reversedBiject {n = Z} x y xpos = []
reversedBiject {n = (S k)} x y Z = case (thisElemthatVect x Z y) of
                                        [] => []
                                        (front :: rest) => [(fst front)]
reversedBiject {n = (S k)} (x :: xs) (y :: ys) (S j) = case (thisElemthatVect (x :: xs) (S j) (y :: ys)) of
                                            [] => []
                                            (front :: rest) => [(fst front)] ++ (reversedBiject (x::xs) (replaceWithZ (y::ys) (fst front)) j)



PermutationBijection: (x: Vect n Nat) -> (y: Vect n Nat) -> (List Nat)
PermutationBijection {n = Z} x y = []
PermutationBijection {n = (S k)} x y = reverse ((reversedBiject x y k))
