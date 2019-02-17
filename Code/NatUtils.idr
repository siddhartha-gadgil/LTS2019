module Tools.NatUtils
--import ZZ
%access public export

{-small auxillary proofs regarding the equality type-}
{-
apZZ : (f: ZZ -> ZZ) -> (n: ZZ) -> (m: ZZ) -> n = m -> f n = f m
apZZ f m m Refl = Refl
-}
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

-- Proof that m<n implies S m = n or S m < n
proofLTimplieseqorLT : (m : Nat) -> (n : Nat) -> (LT m n) -> Either (S m = n) (LT (S m) n)
proofLTimplieseqorLT Z (S Z) (LTESucc LTEZero) = Left Refl
proofLTimplieseqorLT Z (S (S n)) (LTESucc LTEZero) = Right (LTESucc (LTESucc LTEZero))
proofLTimplieseqorLT (S m) (S n) proofSmLTSn = case (proofLTimplieseqorLT m n (fromLteSucc proofSmLTSn)) of
										(Left proofSmeqn) => Left (functionExtendEquality S (S m) n proofSmeqn)
										(Right proofSmLTn) => Right (LTESucc proofSmLTn)


|||The theorem that (m<=n) and (n<=m) implies n=m
lteAndGteImpliesEqual:{m:Nat}-> {n:Nat}->(LTE m n)-> (LTE n m)->(n=m)
lteAndGteImpliesEqual LTEZero LTEZero = Refl
lteAndGteImpliesEqual (LTESucc x) (LTESucc y) = cong (lteAndGteImpliesEqual x y)
|||The theorem (m<=n) implies (m<=(c+n))
plusConstantLeftSide:{m:Nat}->{n:Nat}->(c:Nat)->LTE m n ->LTE m (c+n)
plusConstantLeftSide Z x = x
plusConstantLeftSide (S k) x = lteSuccRight (plusConstantLeftSide k x)

plusConstantLeftPreservesLte:{m:Nat}-> {n:Nat}->(c:Nat)->(LTE m n)->(LTE (c+m) (c+n))
plusConstantLeftPreservesLte Z x = x
plusConstantLeftPreservesLte (S k) x = LTESucc (plusConstantLeftPreservesLte k x)

plusConstantRightPreservesLte:{m:Nat}-> {n:Nat}->(c:Nat)->(LTE m n)->(LTE (m+c) (n+c))
plusConstantRightPreservesLte {m}{n}c x = rewrite (plusCommutative m c)  in (rewrite (plusCommutative n c) in (plusConstantLeftPreservesLte c x))

|||The theorem that for any natural numbers k and m (m<= (S k)*m)
natLteMultNatNat: (k:Nat)->(m:Nat)->(LTE m ((S k)*m))
natLteMultNatNat Z m = rewrite (multOneLeftNeutral m) in (lteRefl)
natLteMultNatNat (S k) m =     plusConstantLeftSide m (natLteMultNatNat  k m)

|||If a <= b, and c <= d, then (a+c) <= (b+d)
lteSumIsLte : (a,b,c,d : Nat) -> LTE a b -> LTE c d -> LTE (a+c) (b+d)
lteSumIsLte a b Z d x LTEZero = rewrite plusZeroRightNeutral a in
																rewrite plusCommutative b d in
																plusConstantLeftSide d x
lteSumIsLte a b (S left) (S right) x (LTESucc y) =
					rewrite sym (plusSuccRightSucc b right) in
					rewrite sym (plusSuccRightSucc a left) in
					(LTESucc (lteSumIsLte a b left right x y))
