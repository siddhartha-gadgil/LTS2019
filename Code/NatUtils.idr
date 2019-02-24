module NatUtils

import Order
--import ZZ

%default total
%access public export

{-small auxillary proofs regarding the equality type-}
{-
apZZ : (f: ZZ -> ZZ) -> (n: ZZ) -> (m: ZZ) -> n = m -> f n = f m
apZZ f m m Refl = Refl
-}

|||difference of Nats, taken from Lecture.intro
sub : (a : Nat) -> (b : Nat) -> (LTE b a) -> Nat
sub a Z LTEZero = a
sub (S a) (S b) (LTESucc proofLTE) = sub a b proofLTE

|||Proof of the type that an implication implies its contrapositive
impliesContrapositive : (a : Type) -> (b : Type) -> (a -> b) -> (b -> Void) -> (a -> Void)
impliesContrapositive a b aImpliesb bFalse x = bFalse (aImpliesb x)

|||Proof that m = n implies f m = f n
--Taken from Lecture.intro with modifications
functionExtendsEquality : (typ : Type) -> (f : typ -> typ) -> (n : typ) -> (m : typ) -> (n = m) -> (f n = f m)
functionExtendsEquality type f m m Refl = Refl

|||Proof that Z is not equal to successor of any natural number
ZIsNotS : {n : Nat} -> (Z = S n) -> Void
ZIsNotS Refl impossible

|||Proof that the sum is greater than its parts
partsLTEsum : (LTE a (a + b), LTE b (a + b))
partsLTEsum {a = Z} {b} = (LTEZero, lteRefl)
partsLTEsum {a = S n} {b} = (LTESucc (fst(partsLTEsum)), lteSuccRight(snd(partsLTEsum)))

||| Proof that a = c, b = d and a <= b implies c <= d
lteSubstitutes : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
				(LTE a b) -> (a = c) -> (b = d) -> (LTE c d)
lteSubstitutes proofLTE Refl Refl = proofLTE

|||Proof that S m = S n implies m = n
predEqual : {a : Nat} -> {b : Nat} -> (S a = S b) -> (a = b)
predEqual {a} {b} proofEq = cong {f = Prelude.Nat.pred} proofEq

|||Proof that a < b implies a <= b
ltImpliesLTE : {a : Nat} -> {b : Nat} -> (LT a b) -> (LTE a b)
ltImpliesLTE proofLTE = lteSuccLeft proofLTE

|||Proof that a = b implies a <= b
eqImpliesLTE : {a : Nat} -> {b : Nat} -> (a = b) -> (LTE a b)
eqImpliesLTE {a = Z} {b = Z} Refl = LTEZero
eqImpliesLTE {a = S k} {b = Z} proofEq = void(SIsNotZ proofEq)
eqImpliesLTE {a = Z} {b = S l} proofEq = void(SIsNotZ (sym proofEq))
eqImpliesLTE {a = S k} {b = S l} proofEq = LTESucc (eqImpliesLTE (predEqual proofEq))

|||The theorem that (a <= b) and (b <= a) implies a = b
lteAndGTEImpliesEqual : {a : Nat} -> {b : Nat} -> (LTE a b) -> (LTE b a) -> (a = b)
lteAndGTEImpliesEqual LTEZero LTEZero = Refl
lteAndGTEImpliesEqual (LTESucc a) (LTESucc b) = cong (lteAndGTEImpliesEqual a b)

|||Proof that a < b implies S a = b or S a < b
ltImpliesEqOrLT : (a : Nat) -> (b : Nat) -> (LT a b) -> Either (S a = b) (LT (S a) b)
ltImpliesEqOrLT Z (S Z) (LTESucc LTEZero) = Left Refl
ltImpliesEqOrLT Z (S (S b)) (LTESucc LTEZero) = Right (LTESucc (LTESucc LTEZero))
ltImpliesEqOrLT (S a) (S b) proofSaLTSb =
	case (ltImpliesEqOrLT a b (fromLteSucc proofSaLTSb)) of
		(Left proofSaEqb) => Left (cong proofSaEqb)
		(Right proofSaLTb) => Right (LTESucc proofSaLTb)

|||Proof that a <= b implies a <= (c + b)
ltePlusConstant : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE a (c + b))
ltePlusConstant {a} {b} c proofLTE = lteSubstitutes (lteTransitive proofLTE (lteAddRight b)) Refl (plusCommutative b c)

|||Proof that a <= b implies (c + a) <= (c + b)
ltePlusConstantLeft : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE (c + a) (c + b))
ltePlusConstantLeft Z proofLTE = proofLTE
ltePlusConstantLeft (S k) proofLTE = LTESucc (ltePlusConstantLeft k proofLTE)

|||Proof that a <= b implies (a + c) <= (b + c)
ltePlusConstantRight : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE (a + c) (b + c))
ltePlusConstantRight {a} {b} c proofLTE = rewrite (plusCommutative a c) in
									rewrite (plusCommutative b c) in
									(ltePlusConstantLeft c proofLTE)

|||Proof that (c + a) <= (c + b) implies a <= b
lteMinusConstantLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LTE (c + a) (c + b)) -> (LTE a b)
lteMinusConstantLeft {c = Z} proofLTE = proofLTE
lteMinusConstantLeft {c = S k} (LTESucc proofLTE) = lteMinusConstantLeft {c = k} proofLTE

|||Proof that (a + c) <= (b + c) implies a <= b
lteMinusConstantRight : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LTE (a + c) (b + c)) -> (LTE a b)
lteMinusConstantRight {a} {b} {c} proofLTE =
	lteMinusConstantLeft (lteSubstitutes proofLTE (plusCommutative a c) (plusCommutative b c))

|||Proof that if a <= b, and c <= d, then (a + c) <= (b + d)
ltePlusIsLTE : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
			(LTE a b) -> (LTE c d) -> (LTE (a + c) (b + d))
ltePlusIsLTE {a = a0} {b = b0} {c = c0} {d = d0} proofLeftLTE proofRightLTE =
	lteTransitive (ltePlusConstantRight {a = a0} {b = b0} c0 proofLeftLTE) (ltePlusConstantLeft {a = c0} {b = d0} b0 proofRightLTE)

|||Proof that m <= (S k) * m
lteMultLeft : (k : Nat) -> (m : Nat) -> (LTE m ((S k) * m))
lteMultLeft Z m = rewrite (multOneLeftNeutral m) in (lteRefl)
lteMultLeft (S k) m = ltePlusConstant m (lteMultLeft k m)

|||Proof that a <= b implies (c * a) <= (c * b)
lteMultConstantLeft : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE (c * a) (c * b))
lteMultConstantLeft {a} {b} Z _ = LTEZero
lteMultConstantLeft {a} {b} (S k) proofLTE =
	ltePlusIsLTE proofLTE (lteMultConstantLeft {a} {b} k proofLTE)

|||Proof that a <= b implies (a * c) <= (b * c)
lteMultConstantRight : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> (LTE (a * c) (b * c))
lteMultConstantRight {a} {b} c proofLTE = rewrite (multCommutative a c) in
									rewrite (multCommutative b c) in
									(lteMultConstantLeft c proofLTE)

|||Proof that if a <= b, and c <= d, then (a * c) <= (b * d)
lteMultIsLTE : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
			(LTE a b) -> (LTE c d) -> (LTE (a * c) (b * d))
lteMultIsLTE {a = a0} {b = b0} {c = c0} {d = d0} proofLeftLTE proofRightLTE =
	lteTransitive (lteMultConstantRight {a = a0} {b = b0} c0 proofLeftLTE) (lteMultConstantLeft {a = c0} {b = d0} b0 proofRightLTE)

|||Proof that n is not lesser than n
succNotLTEn : {n : Nat} -> (LT n n) -> Void
succNotLTEn {n = Z} proofLTE = void (succNotLTEzero proofLTE)
succNotLTEn {n = S k} (LTESucc proofLTE) = succNotLTEn {n = k} proofLTE

|||Proof that a < b implies a != b and !(b < a)
ltImpliesNotEqNotGT : {a : Nat} -> {b : Nat} -> (LT a b) -> (Not (a = b), Not (LT b a))
ltImpliesNotEqNotGT {a} {b = Z} proofLT = void(succNotLTEzero proofLT)
ltImpliesNotEqNotGT {a = Z} {b = S l} proofLT = (ZIsNotS, succNotLTEzero)
ltImpliesNotEqNotGT {a = S k} {b = S l} (LTESucc proofLT) =
	((\proofEq => inductionStep1 (predEqual proofEq)), (\proofLT => inductionStep2 (lteMinusConstantLeft {c = 1} proofLT))) where
		inductionStep1 = fst (ltImpliesNotEqNotGT {a = k} {b = l} proofLT)
		inductionStep2 = snd (ltImpliesNotEqNotGT {a = k} {b = l} proofLT)

|||Proof that a = b implies !(a < b) and !(b < a)
eqImpliesNotLTNotGT : {a : Nat} -> {b : Nat} -> (a = b) -> (Not (LT a b), Not (LT b a))
eqImpliesNotLTNotGT {a = k} {b = k} Refl = (succNotLTEn, succNotLTEn)
