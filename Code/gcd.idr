module gcd

|||add function taken from Intro
add : Nat -> Nat -> Nat
add Z j = j
add (S k) j = S (add k j)

|||mul fucntion taken from Intro
mul : Nat -> Nat -> Nat
mul Z j = Z
mul (S k) j = add j (mul k j)

|||ADivB is the proposition that A divides B
data ADivB : (m : Nat) -> (n: Nat) -> Type where
  OneDivN : (k : Nat) -> ADivB (S Z) k
  MDiv : (k: Nat) -> ADivB m n -> ADivB (mul k m) (mul k n)

|||An example : a proof for 2 divides 4
twoDivFour : ADivB 2 4
twoDivFour = MDiv 2 (OneDivN 2)
