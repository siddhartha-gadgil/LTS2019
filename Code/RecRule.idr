module RecRule

% access public export

recNat : (x : Type) -> x -> (Nat -> x -> x) -> (Nat -> x)
recNat x base step Z = base
recNat x base step (S k) = step k (recNat x base step k)

fctl : Nat -> Nat
fctl = recNat Nat (S Z) step where
  step = \n: Nat => \y : Nat => (S n) * y

recListNat : (x: Type) -> x -> (Nat -> List Nat -> x -> x) -> (List Nat -> x)
recListNat x base step [] = base
recListNat x base step (y :: xs) = step y xs previous where
  previous = recListNat x base step xs

lsum : List Nat -> Nat
lsum = recListNat Nat base step where
  base = Z
  step = \h : Nat => \t : List Nat => \accum : Nat => h + accum
