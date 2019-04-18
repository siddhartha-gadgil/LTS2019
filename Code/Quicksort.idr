module Quicksort

import Data.Vect

partitionVect :  Ord elem => {n : Nat} -> (elem) -> (Vect n elem) -> (l1 : Nat ** (l2 : Nat ** (n = (l1 + l2), (Vect l1 elem, Vect l2 elem))))
partitionVect pivot [] = (0 ** 0 ** (Refl, [], []))
partitionVect pivot (x :: xs) with (partitionVect pivot xs)
 partitionVect pivot (x :: xs) | (l1 ** l2 ** ( equality, v1, v2)) = if (x <= pivot) then (S (l1) ** l2 ** (cong {f = S} equality, (x :: v1), v2)) else
   (l1 ** S (l2) ** (trans (cong {f = S} equality) (plusSuccRightSucc l1 l2), v1, x :: v2))

nLTESn : (n : Nat) -> LTE n (S n)
nLTESn Z = LTEZero
nLTESn (S k) = LTESucc (nLTESn k)


-- qsort : Ord elem => Vect n elem -> (l1 ** l2 ** (Vect (l1 + l2) elem, (l1 + l2) = n))
data PreOrder : (a : Type) -> (a -> a -> Type)-> Type where
  PreOrd : {rel : a -> a -> Type} -> ((x : a) -> rel x x) -> ((x : a) -> (y : a) -> (z : a) -> rel x y -> rel y z -> rel x z) -> PreOrder a rel

data TotalOrder : (a : Type) -> (a -> a -> Type) -> Type where
  TotOrd : {rel : a -> a -> Type} -> PreOrder a rel -> ((x : a) -> (y : a) -> Either (rel x y) (rel y x)) -> TotalOrder a rel

data ForAll : (elem -> Type) -> List elem -> Type where
  None: ForAll p []
  Append: p x -> ForAll p xs -> ForAll p (x :: xs)

forAllConcat : (xs : List elem) -> (ForAll p xs) -> (ys : List elem) -> (ForAll p ys) -> (ForAll p (xs ++ ys))
forAllConcat [] None ys pfys = pfys
forAllConcat (x :: xs) (Append px pfxs) ys pfys = Append px (forAllConcat xs pfxs ys pfys)

forAllBreak : (xs : List elem) -> (ys : List elem) -> (ForAll p (xs ++ ys)) -> (ForAll p xs, ForAll p ys)
forAllBreak [] ys pf = (None, pf)
forAllBreak (x :: xs) ys (Append px pfxs) = let (faxs, fays) = forAllBreak xs ys pfxs in (Append px faxs, fays)


forAllMap : (p : elem -> Type) -> (q : elem -> Type) -> (f : (x : elem) -> p x -> q x) -> (xs : List elem) -> ForAll p xs -> ForAll q xs
forAllMap p q f [] None = None
forAllMap p q f (x :: xs) (Append px pfxs) = Append (f x px) (forAllMap p q f xs pfxs)

data LTEforList : List elem -> List elem -> Type where
  LTEEmpty : LTEforList [] xs
  LTEAppend : LTEforList xs ys -> LTEforList (x :: xs) (y :: ys)

lemma1 : LTEforList xs ys -> LTEforList xs (y :: ys)
lemma1 LTEEmpty = LTEEmpty
lemma1 (LTEAppend pf) = LTEAppend (lemma1 pf)

lemma2 : (xs : List elem) -> LTEforList xs xs
lemma2 [] = LTEEmpty
lemma2 (x :: xs) = LTEAppend (lemma2 xs)

lemma3 : LTEforList xs ys -> LTEforList ys zs -> LTEforList xs zs
lemma3 LTEEmpty _ = LTEEmpty
lemma3 (LTEAppend pf1) (LTEAppend pf2) = LTEAppend (lemma3 pf1 pf2)

data IsSortedAlternate : (elem -> elem -> Type) -> List elem -> Type where
  EmptySorted : IsSortedAlternate lte []
  AppendSorted : {lte : elem -> elem -> Type} -> ForAll (lte x) xs -> IsSortedAlternate lte xs -> IsSortedAlternate lte (x :: xs)

data Permutation : List elem -> List elem -> Type where
  Empty : Permutation [] []
  Split : (xs : List elem) -> (ys : List elem) -> (zs : List elem) -> Permutation xs (ys ++ zs) -> Permutation (x :: xs) (ys ++ (x :: zs))
  Compos : Permutation xs ys -> Permutation ys zs -> Permutation xs zs
  Cat : Permutation ws ys -> Permutation xs zs -> Permutation (ws ++ xs) (ys ++ zs)

forAllPerm : (xs : List elem) -> ForAll p xs -> (ys : List elem) -> Permutation xs ys -> ForAll p ys
forAllPerm [] None [] Empty = None
forAllPerm (x :: xs) (Append px faxs) (ws ++ (x :: ys)) (Split xs ws ys pfperm) =
  let (faws,fays) = forAllBreak ws ys (forAllPerm xs faxs (ws ++ ys) pfperm) in forAllConcat ws faws (x :: ys) (Append px fays)
forAllPerm xs {p} pfxs zs (Compos {ys} permxsys permyszs) = forAllPerm ys (forAllPerm xs pfxs ys permxsys) zs permyszs
forAllPerm (ws ++ xs) pfwscatxs (ys ++ zs) (Cat pfwsys pfxszs) =
  let (pfws,pfxs) = (forAllBreak ws xs pfwscatxs) in forAllConcat ys (forAllPerm ws pfws ys pfwsys) zs (forAllPerm xs pfxs zs pfxszs)

partitionFunc : {p : elem -> Type} -> {q : elem -> Type} -> (f : (x : elem) -> Either (p x) (q x)) ->
                (xs : List elem) -> (ys : List elem ** (zs : List elem ** (LTEforList ys xs,LTEforList zs xs , ForAll p ys, ForAll q zs, Permutation xs (ys ++ zs))))
partitionFunc f [] = ([] ** ([] ** (LTEEmpty, LTEEmpty, None, None, Empty)))
-- partitionFunc f (x :: xs) =
--   let (ys ** (zs ** (pfmn, pfkn, pfys, pfzs, pfperm))) = partitionFunc f xs in
--   case (f x) of
--     (Left px) => ((x :: ys) ** (zs ** (LTESucc pfmn, lteTransitive pfkn (nLTESn (length xs)), Append px pfys, pfzs, Split [] (ys ++ zs) xs (permAddEmpty pfperm))))
