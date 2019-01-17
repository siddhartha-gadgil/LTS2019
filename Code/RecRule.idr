module RecRule

recNat : (x : Type) -> x -> (Nat -> x -> x) -> (Nat -> x)
recNat x base step Z = base
recNat x base step (S k) = step k (recNat x base step k)
