module Intro

sm : List Nat -> Nat
sm [] = 0
sm (x :: xs) = x + (sm xs)

fct : Nat -> Nat
fct Z = 1
fct (S k) = (S k) * (fct k)

fbp : Nat -> (Nat, Nat)
fbp Z = (1, 1)
fbp (S k) = (snd (fbp k), fst (fbp k) + snd (fbp k))

fib : Nat -> Nat
fib n = fst (fbp n)

add : Nat -> Nat -> Nat
add Z j = j
add (S k) j = S (add k j)

mul : Nat -> Nat -> Nat
mul Z j = Z
mul (S k) j = add j (mul k j)

-- Does not work --
sub : (n: Nat) -> (m : Nat) -> (LTE m n) -> Nat
sub n Z LTEZero = n
sub (S right) (S left) (LTESucc x) = sub right left x

-- Seems to work --
subt : (n: Nat) -> (m: Nat) -> {auto smaller = (LTE m n)} -> Nat
subt n Z {smaller = LTEZero} = n
subt (S right) (S left) {smaller = (LTESucc x)} = subt right left
