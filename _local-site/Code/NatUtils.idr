module NatUtils

import Order

%default total
%access public export

|||Proof of the type that an implication implies its contrapositive
impliesContrapositive : (a : Type) -> (b : Type) -> (a -> b) -> (Not b) -> (Not a)
impliesContrapositive a b aImpliesb bFalse x = bFalse (aImpliesb x)

|||Proof that m = n implies f m = f n
--Taken from Lecture.intro with modifications
--Prelude.Basics.cong serves the same function, use cong instead
functionExtendsEquality : (typ : Type) -> (f : typ -> typ) -> (n : typ) -> (m : typ) -> (n = m) -> (f n = f m)
functionExtendsEquality type f m m Refl = Refl

|||An injective predecessor "function"
predInjective : (n : Nat) -> (Not (n = Z)) -> (k ** (S k) = n)
predInjective Z proofNotZ = void (proofNotZ Refl)
predInjective (S k) _ = (k ** Refl)

|||Proof that Z is not equal to successor of any natural number
ZIsNotS : {n : Nat} -> (Not (Z = S n))
ZIsNotS {n} proofEq = SIsNotZ (sym proofEq)

|||difference of Nats, taken from Lecture.intro
sub : (a : Nat) -> (b : Nat) -> (LTE b a) -> Nat
sub a Z LTEZero = a
sub (S a) (S b) (LTESucc proofLTE) = sub a b proofLTE

|||Proof that the sum is greater than its parts
partsLTEsum : (LTE a (a + b), LTE b (a + b))
partsLTEsum {a = Z} {b} = (LTEZero, lteRefl)
partsLTEsum {a = S n} {b} = (LTESucc (fst(partsLTEsum)), lteSuccRight(snd(partsLTEsum)))

|||Proof that S a = S b implies a = b
--Same as succInjective, but implicit
predEqual : {a : Nat} -> {b : Nat} -> (S a = S b) -> (a = b)
predEqual Refl = Refl

|||Proof that a != b implies (S a) != (S b)
notEqualSucc : {a : Nat} -> {b : Nat} -> (Not (a = b)) -> (Not ((S a) = (S b)))
notEqualSucc {a} {b} proofNotEq proofEq = proofNotEq (predEqual proofEq)

|||Proof that (S a) != (S b) implies a != b
notEqualPred : {a : Nat} -> {b : Nat} -> (Not ((S a) = (S b))) -> (Not (a = b))
notEqualPred {a} {b} proofNotEq proofEq = proofNotEq (cong proofEq)

|||Proof that (a + b) = 0 implies a = 0 and b = 0
sumZeroImpliesZero : {a : Nat} -> {b : Nat} -> (a + b = Z) -> (a = Z, b = Z)
sumZeroImpliesZero {a = Z} {b = Z} Refl = (Refl, Refl)
sumZeroImpliesZero {a = Z} {b = S k} proofEq = void (SIsNotZ proofEq)
sumZeroImpliesZero {a = S k} {b} proofEq = void (SIsNotZ proofEq)

|||Proof that a + k = b and k != 0 implies a != b
nonZeroSumNotEqual : {a : Nat} -> {b : Nat} -> {k : Nat} -> (a + k = b) -> (Not (k = Z)) -> (Not (a = b))
nonZeroSumNotEqual {a} {b} {k} proofEq proofNotZ proofaEqb = proofNotZ kEqZ where
	kEqZ = (plusLeftCancel a k Z aPluskEqaPlusZ) where
		aPluskEqaPlusZ = (trans aPluskPlEqbPlusZ (sym ((cong {f = (\n => (n + Z))}) proofaEqb))) where
			aPluskPlEqbPlusZ = rewrite (plusZeroRightNeutral b) in proofEq

|||Proof that (S a) + b = a + (S b)
plusSymmetricInS : {a : Nat} -> {b : Nat} -> ((S a) + b = a + (S b))
plusSymmetricInS {a = Z} {b} = Refl
plusSymmetricInS {a = S k} {b} = cong (plusSymmetricInS {a = k} {b})

|||Proof that a = b implies c * a = c * b
multConstantLeft : {a : Nat} -> {b : Nat} -> (c : Nat) -> (a = b) -> ((c * a) = (c * b))
multConstantLeft {a} {b} Z _ = Refl
multConstantLeft {a} {b} (S k) proofEq =
	trans (cong {f = (\n => n + (k * a))} proofEq) (cong {f = (\n => b + n)} inductiveProofEq) where
		inductiveProofEq = multConstantLeft {a} {b} k proofEq

|||Proof that a = b implies a * c = b * c
multConstantRight : {a : Nat} -> {b : Nat} -> (c : Nat) -> (a = b) -> ((a * c) = (b * c))
multConstantRight {a} {b} c proofEq = rewrite (multCommutative a c) in
								rewrite (multCommutative b c) in
								multConstantLeft c proofEq

|||Proof that c * a != c * b implies a != b
multConstantLeftNot : {a : Nat} -> {b : Nat} -> {c : Nat} -> (Not ((c * a) = (c * b))) -> (Not (a = b))
multConstantLeftNot {a} {b} {c} proofNotEq proofEq = void (proofNotEq (cong {f = (\n => c * n)} proofEq))

|||Proof that a *c != b * c implies a != b
multConstantRightNot : {a : Nat} -> {b : Nat} -> {c : Nat} -> (Not ((a * c) = (b * c))) -> (Not (a = b))
multConstantRightNot {a} {b} {c} proofNotEq proofEq = void (proofNotEq (cong {f = (\n => n * c)} proofEq))

||| Proof that a = c, b = d and a <= b implies c <= d
lteSubstitutes : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
				(LTE a b) -> (a = c) -> (b = d) -> (LTE c d)
lteSubstitutes proofLTE Refl Refl = proofLTE

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

|||Proof that if a<=b then a< c+b when cis not zero
ltePlusConstantLt:(c:Nat)->(Not(c=Z))->LTE a b -> LT a (c+b)
ltePlusConstantLt Z cnotz prf = void (cnotz Refl)
ltePlusConstantLt (S k) cnotz LTEZero = LTESucc LTEZero
ltePlusConstantLt {a=(S j)}{b=(S i)}(S k) cnotz (LTESucc prf) =
	LTESucc (rewrite (sym(plusSuccRightSucc k  i)) in (ltePlusConstantLt (S k) cnotz prf))

|||Proof that a positive number (S m) is less than (S m) multiplied by a number greater that one
ltMultPosByGt1: (k:Nat)->(m:Nat)->(LT (S m) ((S (S k)*(S m))))
ltMultPosByGt1 Z m = rewrite (plusZeroRightNeutral m) in ltePlusConstantLt (S m) SIsNotZ lteRefl
ltMultPosByGt1 (S k) m = ltePlusConstantLt (S m) SIsNotZ (ltImpliesLTE (ltMultPosByGt1 k m))

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


|||Proof that a*b = c*b implies a = c
multRightCancel:(left1:Nat)->(left2:Nat)->(right:Nat)->Not (right =0)->(left1*right=left2*right)->(left1 = left2)
multRightCancel left1 left2 Z rightnotzero prf = void (rightnotzero Refl)
multRightCancel Z Z (S k) rightnotzero prf = Refl
multRightCancel Z (S _) (S _) _ Refl impossible
multRightCancel (S _) Z (S _) _ Refl impossible
multRightCancel (S j) (S i) (S k) rightnotzero prf = cong (multRightCancel j i (S k) rightnotzero (plusLeftCancel (S k) (j*(S k)) (i*(S k))  prf))
|||Proof that a*b = a*c implies b = c
multLeftCancel : (left : Nat) -> (right1 : Nat) -> (right2 : Nat) -> Not(left = 0) -> (left*right1 = left*right2) -> (right1 = right2)
multLeftCancel left right1 right2 lnotz prf =
	multRightCancel right1 right2 left lnotz
	 (rewrite (multCommutative  right1 left) in
	  rewrite (multCommutative  right2 left) in
		prf)

|||Proof that a not LTE b implies b LTE a
-- taken from Lecture.GCD
switchLTE : (n: Nat) -> (m: Nat) -> (contra : (LTE n m) -> Void) -> LTE m n
switchLTE Z m contra = void (contra (LTEZero))
switchLTE (S k) Z contra = LTEZero
switchLTE (S k) (S j) contra =
  LTESucc (switchLTE k j previousContra) where
    previousContra = \evidence : (LTE k j) => contra (LTESucc evidence)

|||Returns Max of two numbers with proof that it is maximum
max : (a : Nat) -> (b : Nat) -> (n : Nat ** ((LTE a n, LTE b n), Either (a=n) (b=n)))
max a b = case isLTE a b of
	(Yes prf) => (b ** ((prf, lteRefl), (Right Refl)))
	(No contra) => (a ** ((lteRefl, (switchLTE a b contra)), (Left Refl)))
