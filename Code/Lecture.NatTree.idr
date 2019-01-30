module NatTree

import Data.Fin

% access public export

data NatTree : Type where
  Leaf : Nat -> NatTree
  Node : NatTree -> NatTree -> NatTree

tsum : NatTree -> Nat
tsum (Leaf k) = k
tsum (Node x y) = (tsum x) + (tsum y)

recNT : (x: Type) -> (Nat -> x) -> (NatTree -> x -> NatTree -> x -> x)
  -> (NatTree -> x)
recNT x f g (Leaf k) = f k
recNT x f g (Node y z) = g y yValue z zValue where
  yValue =  recNT x f g y
  zValue = recNT x f g z

tsumTheHardWay : NatTree -> Nat
tsumTheHardWay = recNT Nat leafCase nodeCase where
  leafCase = \k : Nat => k
  nodeCase = \t1 => \n1 => \t2 => \n2 => n1 + n2

flattenTree : NatTree -> List Nat
flattenTree = recNT (List Nat) leafCase nodeCase where
  leafCase = \k => k :: []
  nodeCase = \t1 => \l1 => \t2 => \l2 => (l1 ++ l2)

data FinNatTree : Type where
  FLeaf : Nat -> FinNatTree
  FNode : (n: Nat) -> ((Fin (S n)) -> FinNatTree) -> FinNatTree

sumFinNat : (n: Nat) -> (Fin n -> Nat) -> Nat
sumFinNat Z f = Z
sumFinNat (S k) f = (f FZ) + tailsum where
  tailsum = sumFinNat k (\ x : (Fin k) => f (FS x))

finSum : FinNatTree -> Nat
finSum (FLeaf k) = k
finSum (FNode n f) = sumFinNat (S n) treeSums where
  treeSums = \index : Fin (S n) => finSum (f index)

  data Evil : Type where
    Diag : (Evil -> Bool) -> Evil

  evil : Evil -> Bool
  evil (Diag f) = not (f (Diag f))

  contra : Bool
  contra = evil (Diag evil)
