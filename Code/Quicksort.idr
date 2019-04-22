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


-- type for a Preorder
data PreOrder : (a : Type) -> (a -> a -> Type)-> Type where
  PreOrd : {rel : a -> a -> Type} -> ((x : a) -> rel x x) -> ((x : a) -> (y : a) -> (z : a) -> rel x y -> rel y z -> rel x z) -> PreOrder a rel

-- type for a total order
data TotalOrder : (a : Type) -> (a -> a -> Type) -> Type where
  TotOrd : {rel : a -> a -> Type} -> PreOrder a rel -> ((x : a) -> (y : a) -> Either (rel y x) (rel x y)) -> TotalOrder a rel

-- type that states the proposition that a property is satisified by all elements of a list
data ForAll : (elem -> Type) -> List elem -> Type where
  None: ForAll p []
  Append: p x -> ForAll p xs -> ForAll p (x :: xs)

-- concatenation of lists obeys the propery forall
forAllConcat : (xs : List elem) -> (ForAll p xs) -> (ys : List elem) -> (ForAll p ys) -> (ForAll p (xs ++ ys))
forAllConcat [] None ys pfys = pfys
forAllConcat (x :: xs) (Append px pfxs) ys pfys = Append px (forAllConcat xs pfxs ys pfys)

-- splitting a list obeys the property forall
forAllBreak : (xs : List elem) -> (ys : List elem) -> (ForAll p (xs ++ ys)) -> (ForAll p xs, ForAll p ys)
forAllBreak [] ys pf = (None, pf)
forAllBreak (x :: xs) ys (Append px pfxs) = let (faxs, fays) = forAllBreak xs ys pfxs in (Append px faxs, fays)

-- mapping lists by a function obeys the forall property
forAllMap : (f : (x : elem) -> p x -> q x) -> (xs : List elem) -> ForAll p xs -> ForAll q xs
forAllMap f [] None = None
forAllMap f (x :: xs) (Append px pfxs) = Append (f x px) (forAllMap f xs pfxs)

-- transitive mapping obeys the forall property
forAllDobMap : (f : (x : elem) -> p x -> q x -> r x) -> (xs : List elem) -> ForAll p xs -> ForAll q xs -> ForAll r xs
forAllDobMap f [] None None = None
forAllDobMap f (x :: xs) (Append px pxs) (Append qx qxs) = Append (f x px qx) (forAllDobMap f xs pxs qxs)

-- type that proves that length of one list is LTE length of the other
data LTEforList : List elem -> List elem -> Type where
  LTEEmpty : LTEforList [] xs
  LTEAppend : LTEforList xs ys -> LTEforList (x :: xs) (y :: ys)

-- LTE for lists holds when an element is added to larger list
lemma1 : LTEforList xs ys -> LTEforList xs (y :: ys)
lemma1 LTEEmpty = LTEEmpty
lemma1 (LTEAppend pf) = LTEAppend (lemma1 pf)

-- LTE for lists holds reflexively
lemma2 : (xs : List elem) -> LTEforList xs xs
lemma2 [] = LTEEmpty
lemma2 (x :: xs) = LTEAppend (lemma2 xs)

-- LTE for lists is transitive
lemma3 : LTEforList xs ys -> LTEforList ys zs -> LTEforList xs zs
lemma3 LTEEmpty _ = LTEEmpty
lemma3 (LTEAppend pf1) (LTEAppend pf2) = LTEAppend (lemma3 pf1 pf2)

-- type for Sorted Lists
data IsSortedAlternate : (elem -> elem -> Type) -> List elem -> Type where
  EmptySorted : IsSortedAlternate rel []
  AppendSorted : {rel : elem -> elem -> Type} -> ForAll (rel x) xs -> IsSortedAlternate rel xs -> IsSortedAlternate rel (x :: xs)

-- type for Permutations
data Permutation : List elem -> List elem -> Type where
  Empty : Permutation [] []
  Split : (xs : List elem) -> (ys : List elem) -> (zs : List elem) -> Permutation xs (ys ++ zs) -> Permutation (x :: xs) (ys ++ (x :: zs))
  Compos : Permutation xs ys -> Permutation ys zs -> Permutation xs zs
  Cat : Permutation ws ys -> Permutation xs zs -> Permutation (ws ++ xs) (ys ++ zs)

-- Permutations follow the for all property
forAllPerm : (xs : List elem) -> ForAll p xs -> (ys : List elem) -> Permutation xs ys -> ForAll p ys
forAllPerm [] None [] Empty = None
forAllPerm (x :: xs) (Append px faxs) (ws ++ (x :: ys)) (Split xs ws ys pfperm) =
  let (faws,fays) = forAllBreak ws ys (forAllPerm xs faxs (ws ++ ys) pfperm) in forAllConcat ws faws (x :: ys) (Append px fays)
forAllPerm xs {p} pfxs zs (Compos {ys} permxsys permyszs) = forAllPerm ys (forAllPerm xs pfxs ys permxsys) zs permyszs
forAllPerm (ws ++ xs) pfwscatxs (ys ++ zs) (Cat pfwsys pfxszs) =
  let (pfws,pfxs) = (forAllBreak ws xs pfwscatxs) in forAllConcat ys (forAllPerm ws pfws ys pfwsys) zs (forAllPerm xs pfxs zs pfxszs)

-- function that partitions a list according to some function on the elements of the list
partitionFunc : {p : elem -> Type} -> {q : elem -> Type} -> (f : (x : elem) -> Either (p x) (q x)) ->
                (xs : List elem) -> (ys : List elem ** (zs : List elem ** (LTEforList ys xs,LTEforList zs xs , ForAll p ys, ForAll q zs, Permutation xs (ys ++ zs))))
partitionFunc f [] = ([] ** ([] ** (LTEEmpty, LTEEmpty, None, None, Empty)))
partitionFunc f (x :: xs) =
  let (ys ** (zs ** (ysltexs, zsltexs, pfys, pfzs, pfperm))) = partitionFunc f xs in
  case (f x) of
    (Left px) => ((x :: ys) ** (zs ** (LTEAppend ysltexs, lemma1 zsltexs, Append px pfys, pfzs, Split xs [] (ys ++ zs) pfperm)))
    (Right qx) => (ys ** ((x :: zs) ** (lemma1 ysltexs, LTEAppend zsltexs, pfys, Append qx pfzs, Split xs ys zs pfperm)))

-- function that partitions according to a total order, and gives a proof that
-- all elements of the first list are smaller than the pivot, pivot is smaller
-- than all elements of the second list, all elements of first list are smaller
-- than second list and the concatenation of the two lists is a permutation of the original list
ordPartition : TotalOrder elem rel -> (pivot : elem) ->
              (xs : List elem) -> (ys : List elem ** (zs : List elem ** (LTEforList ys xs, LTEforList zs xs, ForAll (flip rel pivot) ys, ForAll (rel pivot) zs,
              ForAll (\y => ForAll (rel y) zs) ys, Permutation xs (ys ++ zs))))
ordPartition {rel} (TotOrd (PreOrd refl transt) eith) pivot xs =
  let (ys ** (zs ** (ysltexs, zsltexs, pfys, pfzs, perm))) =
    partitionFunc {p = flip rel pivot} {q = rel pivot} (eith pivot) xs in
    (ys ** (zs ** (ysltexs, zsltexs, pfys, pfzs, lem2 zs pfzs ys pfys, perm)))
    where
      lem2 : (zs : List elem) -> ForAll (rel pivot) zs -> (ys : List elem) -> ForAll (flip rel pivot) ys -> ForAll (\y => ForAll (rel y) zs) ys
      lem2 zs xltzs = forAllMap (\y, yltx => lem y yltx zs xltzs)
        where
          lem : (y : elem) -> rel y pivot -> (zs : List elem) -> ForAll (rel pivot) zs -> ForAll (rel y) zs
          lem y yltx = forAllMap (\z ,xltz => transt y pivot z yltx xltz)

-- proof that the concatenation of the two elements obtained after partitioning
-- using the above function is a sorted list
partSorted : (xs : List elem) -> IsSortedAlternate rel xs -> (ys : List elem) -> IsSortedAlternate rel ys ->
              ForAll (\x => ForAll (rel x) ys) xs -> IsSortedAlternate rel (xs ++ ys)
partSorted [] _ ys sortys _ = sortys
partSorted (x :: xs) {rel} (AppendSorted xltxs sortxs) ys sortys (Append xltys xsltys) =
  AppendSorted xltxsys sortxsys
  where
    sortxsys : IsSortedAlternate rel (xs ++ ys)
    sortxsys = partSorted xs sortxs ys sortys xsltys
    xltxsys :  ForAll (rel x) (xs ++ ys)
    xltxsys = forAllConcat xs xltxs ys xltys

-- auxiliary function used to define quicksort
quicksortAux : TotalOrder elem rel -> (xs : List elem) -> (listBound : List elem) -> (xsbdd : LTEforList xs listBound) ->
                (ys : List elem ** (IsSortedAlternate rel ys, Permutation xs ys))
quicksortAux totorder [] _ _ = ([] ** (EmptySorted, Empty))
quicksortAux {rel} totorder (x :: xs) (xB :: xsB) (LTEAppend xsbdd) =
  --partition
  let (ys ** (zs ** (ysSmall, zsSmall, ysltx, xltzs, ysltzs, perm))) = ordPartition totorder x xs in
  --recursive calls
  let (ys' ** (sortedys', permysys')) = quicksortAux totorder ys xsB (lemma3 ysSmall xsbdd) in
  let (zs' ** (sortedzs', permzszs')) = quicksortAux totorder zs xsB (lemma3 zsSmall xsbdd) in
  --proof that result list is sorted
  let ysltzs' : ForAll (\y => ForAll (rel y) zs') ys
              = forAllMap (\y, yltzs => forAllPerm zs yltzs zs' permzszs') ys ysltzs in
  let ys'ltzs' : ForAll (\y => ForAll (rel y) zs') ys'
                = forAllPerm ys ysltzs' ys' permysys' in
  let ys'ltx : ForAll (flip rel x) ys'
              = forAllPerm ys ysltx ys' permysys' in
  let ys'ltxzs' : ForAll (\y => ForAll (rel y) (x :: zs')) ys'
                  = forAllDobMap (\y => Append) ys' ys'ltx ys'ltzs' in
  let sortedxzs' : IsSortedAlternate rel (x :: zs')
                    = AppendSorted (forAllPerm zs xltzs zs' permzszs') sortedzs' in
  let sortedys'xzs' : IsSortedAlternate rel (ys' ++ x :: zs')
                      = partSorted ys' sortedys' (x :: zs') sortedxzs' ys'ltxzs' in
  -- proof that result is a Permutation
  let perm' : Permutation (ys ++ zs) (ys' ++ zs')
              = Cat permysys' permzszs' in
  let perm'' : Permutation xs (ys' ++ zs')
              = Compos perm perm' in
  let permAll : Permutation (x :: xs) (ys' ++ x :: zs')
              = Split xs ys' zs' perm'' in
  --merging everything together
  ((ys' ++ (x :: zs')) ** (sortedys'xzs', permAll))

-- the quicksort funtion
quickSort : TotalOrder elem rel -> (xs : List elem) -> (ys : List elem ** (IsSortedAlternate rel ys, Permutation xs ys))
quickSort totorder xs = quicksortAux totorder xs xs (lemma2 xs)


--Applying to Nat
reflLTE : (n: Nat) -> LTE n n
reflLTE Z = LTEZero
reflLTE (S k) = LTESucc (reflLTE k)

natLTETrans : (a,b,c : Nat) -> LTE a b -> LTE b c -> LTE a c
natLTETrans Z _ _ _ _ = LTEZero
natLTETrans (S a) (S b) (S c) (LTESucc p) (LTESucc q) = LTESucc (natLTETrans a b c p q)

natLTEEith : (a, b : Nat) -> Either (LTE b a) (LTE a b)
natLTEEith Z _ = Right LTEZero
natLTEEith _ Z = Left LTEZero
natLTEEith (S n) (S m) with (natLTEEith n m)
  | Right x = Right (LTESucc x)
  | Left y = Left (LTESucc y)

totOrdNat : TotalOrder Nat LTE
totOrdNat = TotOrd (PreOrd reflLTE natLTETrans) natLTEEith

quickSortNat : (xs : List Nat) -> (ys : List Nat ** (IsSortedAlternate LTE ys, Permutation xs ys))
quickSortNat xs = quickSort totOrdNat xs
