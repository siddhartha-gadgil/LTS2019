module Tools.NatUtils

%access public export

-- Proof of the type that an implication implies its contrapositive
impliesContrapositive : (A : Type) -> (B : Type) -> (A -> B) -> (B -> Void) -> (A -> Void)
impliesContrapositive typeA typeB proofAimpliesB proofBfalse a = proofBfalse (proofAimpliesB a)

-- Proof that S m = S n implies m = n
meqnSmeqSn : (m : Nat) -> (n : Nat) -> (S m = S n) -> (m = n)
meqnSmeqSn Z Z Refl = Refl
meqnSmeqSn (S k) (S k) Refl = Refl

-- Proof that m = n implies f(m) = f(n), taken from Lecture.intro (apNat)
functionExtendEquality : (f : Nat -> Nat) -> (n : Nat) -> (m : Nat) -> (n = m) -> (f n = f m)
functionExtendEquality f m m Refl = Refl

-- Proof that m != n implies S m != S n
proofSmneqSn : (m : Nat) -> (n : Nat) -> ((m = n) -> Void) -> ((S m = S n) -> Void)
proofSmneqSn m n proofmneqn = impliesContrapositive (S m = S n) (m = n) (meqnSmeqSn m n) proofmneqn
