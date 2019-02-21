module SandBox

--putting all files for checking here

-- IMPORTANT rewrite (left = right) replaces all instances of right with left

functionExtendsEquality : (typ : Type) -> (f : typ -> typ) -> (n : typ) -> (m : typ) -> (n = m) -> (f n = f m)
functionExtendsEquality type f m m Refl = Refl

||| Proof that m<n implies S m = n or S m < n
proofLTimplieseqorLT : (m : Nat) -> (n : Nat) -> (LT m n) -> Either (S m = n) (LT (S m) n)
proofLTimplieseqorLT Z (S Z) (LTESucc LTEZero) = Left Refl
proofLTimplieseqorLT Z (S (S n)) (LTESucc LTEZero) = Right (LTESucc (LTESucc LTEZero))
proofLTimplieseqorLT (S m) (S n) proofSmLTSn = case (proofLTimplieseqorLT m n (fromLteSucc proofSmLTSn)) of
										(Left proofSmeqn) => Left (functionExtendsEquality Nat S (S m) n proofSmeqn)
										(Right proofSmLTn) => Right (LTESucc proofSmLTn)



|||Auxilliary proof for euclidDivide
--Proof to finish euclidDivide, couldn't add it as a where clause within euclidDivide. If someone knows how to do that, please do so.
extendedEqualityProof : (a : Nat) -> (b : Nat) -> (q : Nat) -> (r : Nat)->
					((S r) = b) -> (a = r + (q * b)) -> (S a = (S q) * b)
extendedEqualityProof a b q r proofSmlEq proofBigEq =
	trans (functionExtendsEquality Nat S a (r + (q * b)) proofBigEq) (plusConstantRight (S r) b (q * b) proofSmlEq)

||| Given a, b, and a proof that b != 0, returns (q, r) and proofs that a = bq + r, r < b
--removed possible problems with Rohit's
euclidDivide : (a : Nat) -> (b : Nat) -> (b = Z -> Void) -> (r : Nat ** (q : Nat ** ((a = r + (q * b)), LT r b)))
euclidDivide _ Z proofeq = void(proofeq Refl)
euclidDivide Z (S k) SIsNotZ = (Z ** (Z ** (Refl, LTESucc LTEZero)))
euclidDivide (S n) (S k) SIsNotZ =
	case (euclidDivide n (S k) SIsNotZ) of
		(r ** (q ** (equalityProof, ltproof))) =>
			case (proofLTimplieseqorLT r (S k) ltproof) of
				(Right proofSrLTSk) => ((S r) ** (q ** ((functionExtendsEquality Nat S n (r + (q * (S k))) equalityProof), proofSrLTSk)))
				(Left proofSreqSk) => (Z ** ((S q) ** ((extendedEqualityProof n (S k) q r proofSreqSk equalityProof), LTESucc LTEZero)))

|||Type of proof that d divides a
isDivisible : (a : Nat) -> (d : Nat) -> (Not (d = Z))-> Type
isDivisible a d proofNotZ = (n : Nat ** a = n * d)

|||Proof that all natural numbers divide zero
zeroDivisible : {n : Nat} ->  isDivisible Z (S n) SIsNotZ
zeroDivisible {n} = (Z ** sym (multZeroLeftZero (S n)))

|||Proof that 1 divides all natural numbers
oneDivides : {n : Nat} -> isDivisible n (S Z) SIsNotZ
oneDivides {n} = (n ** rewrite multOneRightNeutral n in Refl)

|||Proof that all natural numbers divide themselves
divisionReflexive : {n : Nat} -> (isDivisible (S n) (S n) SIsNotZ)
divisionReflexive {n} = (S Z ** rewrite multOneLeftNeutral n in Refl)

|||Type of proof that d is a common divisor of a and b
isCommonDivisor : (a : Nat) -> (b : Nat) -> (d : Nat) -> (Not (d = Z)) -> Type
isCommonDivisor a b d proofNotZ = (isDivisible a d proofNotZ, isDivisible b d proofNotZ)

|||Proof that 1 is a common divisor of all pairs of natural numbers
oneCommonDivisor : {a : Nat} -> (b : Nat) -> (isCommonDivisor a b (S Z) SIsNotZ)
oneCommonDivisor {a} {b} = (oneDivides, oneDivides)

|||Proof that n is a common divisor of n and 0
zeroCommonDivisorRight : {n : Nat} -> (isCommonDivisor (S n) Z (S n) SIsNotZ)
zeroCommonDivisorRight {n} = (divisionReflexive, zeroDivisible)

|||Proof that n is a common divisor of 0 and n
zeroCommonDivisorLeft : {n : Nat} -> (isCommonDivisor Z (S n) (S n) SIsNotZ)
zeroCommonDivisorLeft {n} = (zeroDivisible, divisionReflexive)

|||Proof that a common divisor of (a, b) is a common divisor of (b, a)
commonDivisorSymmetric : {a : Nat} -> {b : Nat} -> {d : Nat} -> (isCommonDivisor a b d proofNotZ) -> (isCommonDivisor b a d proofNotZ)
commonDivisorSymmetric {a} {b} {d} (proofDividesa, proofDividesb) = (proofDividesb, proofDividesa)

|||Proof that d divides a implies d divides c * a
dividesMultiple : {a : Nat} -> {d : Nat} -> (isDivisible a d proofNotZ) -> (c : Nat)-> (isDivisible (c * a) d proofNotZ)
dividesMultiple {d} (n ** Refl) c = ((c * n) ** (rewrite (multAssociative c n d) in Refl))

|||Proof of distributivity
distributeProof: (a : Nat) -> (b : Nat) -> (d : Nat) -> (m : Nat) -> (n : Nat) ->
(a = m * d) -> (b = n * d) -> ((a + b) = (m + n) * d)
distributeProof a b d m n proofDividesa proofDividesb =
	rewrite (multDistributesOverPlusLeft m n d) in
		(trans (the (a + b = (m * d) + b) (v1)) v2) where
			v1 = plusConstantRight a (m * d) b proofDividesa
			v2 = plusConstantLeft b (n * d) (m * d) proofDividesb

|||Proof that d is a common divisor of a and b implies d divides a + b
dividesSum :  {a : Nat} -> {b : Nat} -> {d : Nat} -> (isCommonDivisor a b d proofNotZ)-> (isDivisible (a + b) d proofNotZ)
dividesSum {a} {b} {d} ((m ** proofDividesa), (n ** proofDividesb)) =
	((m + n) ** (distributeProof a b d m n proofDividesa proofDividesb))

|||difference of Nats, taken from Lecture.intro
sub : (m : Nat) -> (n : Nat) -> (LTE n m) -> Nat
sub m Z LTEZero = m
sub (S m) (S n) (LTESucc proofleq) = sub m n proofleq

|||Proof that the sum is greater than its parts
partsLTEsum : (LTE a (a + b), LTE b (a + b))
partsLTEsum {a = Z} {b} = (LTEZero, lteRefl)
partsLTEsum {a = S n} {b} = (LTESucc (fst(partsLTEsum)), lteSuccRight(snd(partsLTEsum)))

||| Proof that a = c, b = d and a <= b implies c <= d
lteSubstitutes : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
				(LTE a b) -> (a = c) -> (b = d) -> (LTE c d)
lteSubstitutes {a} {b} proofaLTEb Refl Refl = proofaLTEb

|||Proof that (c + a) <= (c + b) implies a <= b
lteRemoveConstantLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LTE (c + a) (c + b)) -> (LTE a b)
lteRemoveConstantLeft {a} {b} {c = Z} proofLTE = proofLTE
lteRemoveConstantLeft {a} {b} {c = S k} (LTESucc proofLTE) =
	lteRemoveConstantLeft {a} {b} {c = k} proofLTE

|||Proof that (a + c) <= (b + c) implies a <= b
lteRemoveConstantRight : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LTE (a + c) (b + c)) -> (LTE a b)
lteRemoveConstantRight {a} {b} {c} proofapluscLTEbplusc =
	lteRemoveConstantLeft (lteSubstitutes proofapluscLTEbplusc (plusCommutative a c) (plusCommutative b c))

{-
|||Proof that a = m * d, b = n * d and a LTE b implies m LTE n
proofmLTEn : {m : Nat} -> {n : Nat} -> {d : Nat} -> (Not (d = Z)) -> (LTE (m * d) (n * d)) -> (LTE m n)
proofmLTEn {m} {n} {d = Z} proofNotZ _ = void(proofNotZ Refl)
proofmLTEn {m} {n} {d = S Z} SIsNotZ proofmLTEn =
	lteSubstitutes proofmLTEn (multOneRightNeutral m) (multOneRightNeutral n) where
proofmLTEn {m} {n} {d = S (S k)} SIsNotZ proofadLTEbd =
	proofmLTEn {m} {n} {d = S k} SIsNotZ proofFinal where
		proofFinal = lteSubstitutes proofStep3 (multCommutative (S k) m) (multCommutative (S k) n) where
			proofStep3 = lteRemoveConstantLeft proofStep2 where
				proofstep2 = lteSubstitutes proofaLTEb (multCommutative a (S (S k))) (multCommutative b (S (S k)))

|||Proof that d divides (a + b) and d divides a implies d divides b
dividesDifference : {a : Nat} -> {b : Nat} -> {d : Nat} -> (isCommonDivisor (a + b) a d) -> (isDivisible b d)
dividesDifference {a} {b} {d} ((m ** proofDividesaplusb), (n ** proofDividesa)) =
	(minus m n (proofmLTEn  ** proofSubEq)) where
		proofSubEq : {a : Nat} -> {b : Nat} -> {d : Nat} -> {m : Nat} -> {n : Nat} -> (a + b = m * d) -> (a = n * d) -> (b = (sub m n) * d)

|||Proof that d is a common divisor of a and b implies d divides a * x + b * y
dividesLinearCombination :  {a : Nat} -> {b : Nat} -> {d : Nat} -> (isCommonDivisor a b d) ->
						(x : Nat) -> (y : Nat) -> (isDivisible ((x * a) + (y * b)) d)
dividesLinearCombination {a} {b} {d} (dDividesa, dDividesb) x y =
	dividesSum (dividesax, dividesby) where
		dividesax = dividesMultiple dDividesa x
		dividesby = dividesMultiple dDividesb y

|||Proof d divides a and a = b implies d divides b
eqConservesDivisible : {a : Nat} -> {b : Nat} -> {d : Nat} -> {proofNotZero : Not (d = Z)} (isDivisible a d proofNotZero) -> (a = b) -> (isDivisible b d proofNotZero)
eqConservesDivisible {a} {d} (n ** proofDivides) Refl = (n ** proofDivides)

--Returns the GCD of a and b with proof that it is the GCD
gcd : (a : Nat) -> (b : Nat) -> (d : Nat ** ((isCommonDivisor a b d), (n : Nat) -> (isCommonDivisor a b n) -> (isDivisible d n)))
gcd a Z = (a ** (zeroCommonDivisorRight, (\n : Nat => (\proofCommonDivisor => fst(proofCommonDivisor)))))
gcd Z a = (a ** (zeroCommonDivisorLeft, (\n : Nat => (\proofCommonDivisor => snd(proofCommonDivisor)))))
gcd (S a) (S b) = case (euclidDivide (S a) (S b) SIsNotZ) of
				(r ** (q ** (equalProof, ltProof))) =>
					case gcd (S b) r of
						(d ** (commonDivisorProof,  largestDivisorProof)) =>
							(d ** ((dDividesSa, fst(commonDivisorProof)) ** _proofcommDivsorssdivD_) where
								dDividesSa = dividesLinearCombination commonDivisorProof
-}
