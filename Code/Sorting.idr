module Sorting

--To build permutations
data IsPer : List Nat -> List Nat -> Type where
  ReflPer : (m : List Nat) -> IsPer m m
  SymPer : IsPer m n -> IsPer n m
  TransPer : IsPer m n -> IsPer n p -> IsPer m p
  HeadPer : IsPer m n -> IsPer a b -> IsPer (m++a) (m++b)
  TailPer : IsPer m n -> IsPer a b -> IsPer (a++m) (b++n)
  MixPer : IsPer m n -> IsPer a b -> IsPer (a++m) (n++b)
