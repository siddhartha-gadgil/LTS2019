module Intro

% access public export

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

public export
add : Nat -> Nat -> Nat
add Z j = j
add (S k) j = S (add k j)

mul : Nat -> Nat -> Nat
mul Z j = Z
mul (S k) j = add j (mul k j)

sub : (n: Nat) -> (m : Nat) -> (LTE m n) -> Nat
sub n Z LTEZero = n
sub (S right) (S left) (LTESucc x) = sub right left x

oneLTEFour : LTE 1 4
oneLTEFour = LTESucc LTEZero

fourMinusOne : Nat
fourMinusOne = sub 4 1 oneLTEFour

reflLTE : (n: Nat) -> LTE n n
reflLTE Z = LTEZero
reflLTE (S k) = LTESucc (reflLTE k)

sillyZero: Nat -> Nat
sillyZero n = sub n n (reflLTE n)

idNat : Nat -> Nat
idNat = \x => x

loop: Nat -> Nat
loop k = loop (S k)

isFactor : Nat -> Nat -> Type
isFactor m n = (k : Nat ** (m * k = n))
