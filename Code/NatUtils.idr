module Tools.NatUtils
import ZZ
%access public export

{-small auxillary proofs regarding the equality type-}

apZZ : (f: ZZ -> ZZ) -> (n: ZZ) -> (m: ZZ) -> n = m -> f n = f m
apZZ f m m Refl = Refl

addsame : (t: ZZ)->(n:ZZ)->(m:ZZ)-> n = m -> (n+t)=(m+t)
addsame t m m Refl=Refl

addeqns : (a:ZZ)->(b:ZZ)-> a=b -> (p:ZZ)->(q:ZZ)-> p=q -> ((a+p)=(b+q))
addeqns a a Refl p p Refl=Refl

equality1 : (p:ZZ)->(k:ZZ)->(a:ZZ)-> (a=p*k)->(l:ZZ)->(b:ZZ)->(b=p*l)->(a+b)=(p*k + p*l)
equality1 p k a x l b y = addeqns a (p*k) x b (p*l) y

equality2 : (p:ZZ)->(k:ZZ)->(a:ZZ)-> (a=p*k)->(l:ZZ)->(b:ZZ)->(b=p*l)->(a+b)=p*(k+l)
equality2 p k a x l b y = trans (equality1 p k a x l b y) (sym (multDistributesOverPlusRightZ p k l))

{-end of auxillary proofs-}

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
