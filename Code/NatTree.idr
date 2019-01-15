module NatTree

data NatTree : Type where
  Leaf : Nat -> NatTree
  Node : NatTree -> NatTree -> NatTree

tsum : NatTree -> Nat
tsum (Leaf k) = k
tsum (Node x y) = (tsum x) + (tsum y)
