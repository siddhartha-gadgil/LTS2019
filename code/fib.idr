module Fibonacci

fibpair: Nat -> (Nat, Nat)
fibpair Z = (0, 1)
fibpair (S k) = case (fibpair k) of
                     (a, b) => (b, a + b)
