module Tools.NatUtils
--import ZZ
%access public export

{-small auxillary proofs regarding the equality type-}
{-
apZZ : (f: ZZ -> ZZ) -> (n: ZZ) -> (m: ZZ) -> n = m -> f n = f m
apZZ f m m Refl = Refl
-}
%access public export

|||difference of Nats, taken from Lecture.intro
sub : (m : Nat) -> (n : Nat) -> (LTE n m) -> Nat
sub m Z LTEZero = m
sub (S m) (S n) (LTESucc proofLTE) = sub m n proofLTE

|||Proof of the type that an implication implies its contrapositive
impliesContrapositive : (a : Type) -> (b : Type) -> (a -> b) -> (b -> Void) -> (a -> Void)
impliesContrapositive a b aImpliesb bFalse x = bFalse (aImpliesb x)

|||Proof that m = n implies f m = f n
--Taken from Lecture.intro with modifications
functionExtendsEquality : (typ : Type) -> (f : typ -> typ) -> (n : typ) -> (m : typ) -> (n = m) -> (f n = f m)
functionExtendsEquality type f m m Refl = Refl

|||Proof that Z is not equal to successor of any natural number
ZIsNotS : {k : Nat} -> (Z = S k) -> Void
ZIsNotS Refl impossible

|||Proof that the sum is greater than its parts
partsLTEsum : (LTE a (a + b), LTE b (a + b))
partsLTEsum {a = Z} {b} = (LTEZero, lteRefl)
partsLTEsum {a = S n} {b} = (LTESucc (fst(partsLTEsum)), lteSuccRight(snd(partsLTEsum)))

||| Proof that a = c, b = d and a <= b implies c <= d
lteSubstitutes : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
				(LTE a b) -> (a = c) -> (b = d) -> (LTE c d)
lteSubstitutes {a} {b} proofLTE Refl Refl = proofLTE

|||Proof that S m = S n implies m = n
predEqual : (m : Nat) -> (n : Nat) -> (S m = S n) -> (m = n)
predEqual m n proofEq = functionExtendsEquality Nat Prelude.Nat.pred (S m) (S n) proofEq

|||Proof that a < b implies a <= b
ltImpliesLTE : {a : Nat} -> {b : Nat} -> (LT a b) -> (LTE a b)
ltImpliesLTE proofLTE = lteSuccLeft proofLTE

|||Proof that a = b implies a <= b
eqImpliesLTE : {a : Nat} -> {b : Nat} -> (a = b) -> (LTE a b)
eqImpliesLTE {a = Z} {b = Z} Refl = LTEZero
eqImpliesLTE {a = S k} {b = Z} proofEq = void(SIsNotZ proofEq)
eqImpliesLTE {a = Z} {b = S l} proofEq = void(SIsNotZ (sym proofEq))
eqImpliesLTE {a = S k} {b = S l} proofEq = LTESucc (eqImpliesLTE (predEqual k l proofEq))

|||The theorem that (m <= n) and (n <= m) implies n = m
lteAndGTEImpliesEqual : {m : Nat} -> {n : Nat} -> (LTE m n) -> (LTE n m) -> (n = m)
lteAndGTEImpliesEqual LTEZero LTEZero = Refl
lteAndGTEImpliesEqual (LTESucc x) (LTESucc y) = cong (lteAndGTEImpliesEqual x y)

|||Proof that m < n implies S m = n or S m < n
ltImpliesEqOrLT : (m : Nat) -> (n : Nat) -> (LT m n) -> Either (S m = n) (LT (S m) n)
ltImpliesEqOrLT Z (S Z) (LTESucc LTEZero) = Left Refl
ltImpliesEqOrLT Z (S (S n)) (LTESucc LTEZero) = Right (LTESucc (LTESucc LTEZero))
ltImpliesEqOrLT (S m) (S n) proofSmLTSn =
	case (ltImpliesEqOrLT m n (fromLteSucc proofSmLTSn)) of
		(Left proofSmEqn) => Left (functionExtendsEquality Nat S (S m) n proofSmEqn)
		(Right proofSmLTn) => Right (LTESucc proofSmLTn)

|||Proof that (c + a) <= (c + b) implies a <= b
lteRemoveConstantLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LTE (c + a) (c + b)) -> (LTE a b)
lteRemoveConstantLeft {a} {b} {c = Z} proofLTE = proofLTE
lteRemoveConstantLeft {a} {b} {c = S k} (LTESucc proofLTE) =
	lteRemoveConstantLeft {a} {b} {c = k} proofLTE

|||Proof that (a + c) <= (b + c) implies a <= b
lteRemoveConstantRight : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LTE (a + c) (b + c)) -> (LTE a b)
lteRemoveConstantRight {a} {b} {c} proofLTE =
	lteRemoveConstantLeft (lteSubstitutes proofLTE (plusCommutative a c) (plusCommutative b c))

|||Proof that m <= n implies m <= (c + n)
lteAddConstant : {m : Nat} -> {n : Nat} -> (c : Nat)-> (LTE m n) -> (LTE m (c + n))
lteAddConstant Z proofLTE = proofLTE
lteAddConstant (S k) proofLTE = lteSuccRight (lteAddConstant k proofLTE)

|||Proof that a <= b implies (c + a) <= (c + b)
lteAddConstantLeft : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE (c + a) (c + b))
lteAddConstantLeft Z proofLTE = proofLTE
lteAddConstantLeft (S k) proofLTE = LTESucc (lteAddConstantLeft k proofLTE)

|||Proof that a <= b implies (a + c) <= (b + c)
lteAddConstantRight : {m : Nat} -> {n : Nat} -> (c : Nat) -> (LTE m n) -> (LTE (m + c) (n + c))
lteAddConstantRight {m} {n} c proofLTE = rewrite (plusCommutative m c) in
									rewrite (plusCommutative n c) in
									(lteAddConstantLeft c proofLTE)

|||Proof that for any natural numbers k and m, m <= (S k) * m
natLTEMultNatNat: (k : Nat) -> (m : Nat) -> (LTE m ((S k) * m))
natLTEMultNatNat Z m = rewrite (multOneLeftNeutral m) in (lteRefl)
natLTEMultNatNat (S k) m = lteAddConstant m (natLTEMultNatNat k m)

|||If a <= b, and c <= d, then (a + c) <= (b + d)
lteSumIsLte : (a, b, c, d : Nat) -> (LTE a b) -> (LTE c d) -> (LTE (a + c) (b + d))
lteSumIsLte a b Z d proofLTE LTEZero = rewrite plusZeroRightNeutral a in
								rewrite plusCommutative b d in
								lteAddConstant d proofLTE
lteSumIsLte a b (S left) (S right) proofLTEleft (LTESucc proofLTEright) =
	rewrite sym (plusSuccRightSucc b right) in
	rewrite sym (plusSuccRightSucc a left) in
	(LTESucc (lteSumIsLte a b left right proofLTEleft proofLTEright))

|||Proof that n is not lesser than n
succNotLTEn : {n : Nat} -> (LT n n) -> Void
succNotLTEn {n = Z} proofLTE = void (succNotLTEzero proofLTE)
succNotLTEn {n = S k} (LTESucc proofLTE) =
	impliesContrapositive (LT (S k) (S k)) (LT k k) (lteRemoveConstantLeft {c = 1}) (succNotLTEn {n = k}) (LTESucc proofLTE)

|||Proof that a < b implies a != b and !(b < a)
ltImpliesNotEqNotGT : {a : Nat} -> {b : Nat} -> (LT a b) -> (Not (a = b), Not (LT b a))
ltImpliesNotEqNotGT {a} {b = Z} proofLT = void(succNotLTEzero proofLT)
ltImpliesNotEqNotGT {a = Z} {b = S l} proofLT = (ZIsNotS, succNotLTEzero)
ltImpliesNotEqNotGT {a = S k} {b = S l} (LTESucc proofLT) =
	((impliesContrapositive (S k = S l) (k = l) (predEqual k l) inductionStep1), (impliesContrapositive (LT (S l) (S k)) (LT l k) (lteRemoveConstantLeft {c = 1}) inductionStep2)) where
		inductionStep1 = fst (ltImpliesNotEqNotGT proofLT)
		inductionStep2 = snd (ltImpliesNotEqNotGT proofLT)

|||Proof that a = b implies !(a < b) and !(b < a)
eqImpliesNotLTNotGT : {a : Nat} -> {b : Nat} -> (a = b) -> (Not (LT a b), Not (LT b a))
eqImpliesNotLTNotGT {a = k} {b = k} Refl = (succNotLTEn, succNotLTEn)
