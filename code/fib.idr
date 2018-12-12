module Fibonacci

fibpair: Nat -> (Nat, Nat)
fibpair Z = (1, 1)
fibpair (S k) = case (fibpair k) of
                     (a, b) => (b, a + b)

append : List a -> a -> List a
append [] x = x :: []
append (y :: xs) x = y :: (append xs x)

fiblist: Nat -> List (Nat)
fiblist Z = []
fiblist (S k) = case (fibpair k) of
                     (a, b) => append (fiblist k) a

tuple: Nat -> Type
tuple Z = Unit
tuple (S k) = (Nat, tuple k)

fibtup: (n: Nat) -> tuple n
fibtup Z = ()
fibtup (S k) = case (fibpair k) of
                    (a, b) => (a, fibtup k)


apptup: (n: Nat) -> tuple n -> Nat -> tuple (succ n)
apptup Z () k = (k, ())
apptup (S j) (a, b) k = (a, tail) where
  tail = apptup j b k

rev: (n: Nat) -> tuple n -> tuple n
rev Z () = ()
rev (S k) (a, b) = apptup k (rev k b) a

revv: {n: Nat} -> tuple n -> tuple n
revv {n = Z} () = ()
revv {n = (S k)} (a, b) = apptup k (revv b) a
