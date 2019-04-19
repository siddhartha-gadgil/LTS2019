module sandboxNatUtils

%default total
%access public export

|||An injective predecessor "function"
predInjective : (n : Nat) -> (Not (n = Z)) -> (k ** (S k) = n)
predInjective Z proofNotZ = void (proofNotZ Refl)
predInjective (S k) _ = (k ** Refl)

|||Proof that Z is not equal to successor of any natural number
ZIsNotS : {n : Nat} -> (Not (Z = S n))
ZIsNotS {n} proofEq = SIsNotZ (sym proofEq)

|||Proof that S a = S b implies a = b
--Same as succInjective, but implicit
predEqual : {a : Nat} -> {b : Nat} -> (S a = S b) -> (a = b)
predEqual Refl = Refl

|||Proof that the sum is greater than its parts
partsLTEsum : (a : Nat) -> (b : Nat) -> (LTE a (a + b), LTE b (a + b))
partsLTEsum Z b = (LTEZero, lteRefl)
partsLTEsum (S n) b = (LTESucc (fst (partsLTEsum n b)), lteSuccRight(snd (partsLTEsum n b)))

|||Proof that a != b implies (S a) != (S b)
notEqualSucc : {a : Nat} -> {b : Nat} -> (Not (a = b)) -> (Not ((S a) = (S b)))
notEqualSucc {a} {b} proofNotEq proofEq = proofNotEq (predEqual proofEq)

|||Proof that (S a) != (S b) implies a != b
notEqualPred : {a : Nat} -> {b : Nat} -> (Not ((S a) = (S b))) -> (Not (a = b))
notEqualPred {a} {b} proofNotEq proofEq = proofNotEq (cong proofEq)

|||Proof of distributivity
distributeProof: (a : Nat) -> (b : Nat) -> (d : Nat) -> (m : Nat) -> (n : Nat) ->
(a = m * d) -> (b = n * d) -> ((a + b) = (m + n) * d)
distributeProof a b d m n proofDividesa proofDividesb =
	rewrite (multDistributesOverPlusLeft m n d) in
		(trans (the (a + b = (m * d) + b) (v1)) v2) where
			v1 = plusConstantRight a (m * d) b proofDividesa
			v2 = plusConstantLeft b (n * d) (m * d) proofDividesb

|||Proof that a < b implies a != b
ltImpliesNotEq : {a : Nat} -> {b : Nat} -> (LT a b) -> (Not (a = b))
ltImpliesNotEq {a} {b = Z} proofLT proofEq = succNotLTEzero proofLT
ltImpliesNotEq {a = Z} {b = (S l)} proofLT proofEq = ZIsNotS proofEq
ltImpliesNotEq {a = (S k)} {b = (S l)} (LTESucc proofLT) proofEq = ltImpliesNotEq {a = k} {b = l} proofLT (predEqual proofEq)

|||Proof that a < b implies S a = b or S a < b
ltImpliesEqOrLT : (a : Nat) -> (b : Nat) -> (LT a b) -> Either (S a = b) (LT (S a) b)
ltImpliesEqOrLT Z (S Z) (LTESucc LTEZero) = Left Refl
ltImpliesEqOrLT Z (S (S b)) (LTESucc LTEZero) = Right (LTESucc (LTESucc LTEZero))
ltImpliesEqOrLT (S a) (S b) proofSaLTSb =
	case (ltImpliesEqOrLT a b (fromLteSucc proofSaLTSb)) of
		(Left proofSaEqb) => Left (cong proofSaEqb)
		(Right proofSaLTb) => Right (LTESucc proofSaLTb)

|||Proof that (a + b) = 0 implies a = 0 and b = 0
sumZeroImpliesZero : {a : Nat} -> {b : Nat} -> (a + b = Z) -> (a = Z, b = Z)
sumZeroImpliesZero {a = Z} {b = Z} Refl = (Refl, Refl)
sumZeroImpliesZero {a = Z} {b = S k} proofEq = void (SIsNotZ proofEq)
sumZeroImpliesZero {a = S k} {b} proofEq = void (SIsNotZ proofEq)

|||Proof that (a * b) = 0 implies a = 0 or b = 0
multZeroImpliesZero : {a : Nat} -> {b : Nat} -> (a * b = Z) -> Either (a = Z) (b = Z)
multZeroImpliesZero {a = Z} {b} proofZ = Left Refl
multZeroImpliesZero {a = S k} {b = Z} proofZ = Right Refl
multZeroImpliesZero {a = S k} {b = S l} proofZ = void (SIsNotZ proofZ)

|||Proof that (a * b) = 1 implies a = 1 and b = 1
multOneImpliesOne : {a : Nat} -> {b : Nat} -> (a * b = 1) -> (a = 1, b = 1)
multOneImpliesOne {a = Z} {b} proofEq = void (ZIsNotS proofEq)
multOneImpliesOne {a} {b = Z} proofEq = void (ZIsNotS (rewrite (sym (multZeroRightZero a)) in proofEq))
multOneImpliesOne {a = S Z} {b = S Z} _ = (Refl, Refl)
multOneImpliesOne {a = (S (S k))} {b = (S l)} proofEq = void (ltImpliesNotEq (lteTransitive (LTESucc (LTESucc LTEZero)) (fst (partsLTEsum (S (S k)) (l * (S (S k)))))) (sym (rewrite (multCommutative (S l) (S (S k))) in proofEq)))
multOneImpliesOne {a = (S k)} {b = (S (S l))} proofEq = void (ltImpliesNotEq (lteTransitive (LTESucc (LTESucc LTEZero)) (fst (partsLTEsum (S (S l)) (k * (S (S l)))))) (sym proofEq))

|||Proof that a + k = b and k != 0 implies a != b
nonZeroSumNotEqual : {a : Nat} -> {b : Nat} -> {k : Nat} -> (a + k = b) -> (Not (k = Z)) -> (Not (a = b))
nonZeroSumNotEqual {a} {b} {k} proofEq proofNotZ proofaEqb = proofNotZ kEqZ where
	kEqZ = (plusLeftCancel a k Z aPluskEqaPlusZ) where
		aPluskEqaPlusZ = (trans aPluskPlEqbPlusZ (sym ((cong {f = (\n => (n + Z))}) proofaEqb))) where
			aPluskPlEqbPlusZ = rewrite (plusZeroRightNeutral b) in proofEq

|||Proof that a + k = b and a != b implies k != 0
nonEqualSumNotZero : {a : Nat} -> {b : Nat} -> {k : Nat} -> (a + k = b) -> (Not (a = b)) -> (Not (k = Z))
nonEqualSumNotZero {a} {b} {k} proofEq proofaNotEqb proofkEqZ =
	proofaNotEqb proofaEqb where
		proofaEqb = rewrite (plusCommutative Z a) in
					rewrite (sym proofkEqZ) in proofEq

|||Proof that a != 0 implies a + b != 0
nonZeroSumNotZeroLeft :  {a : Nat} -> {b : Nat} -> (Not (a = Z)) -> Not (a + b = Z)
nonZeroSumNotZeroLeft {a} {b} proofNotZero proofZero = proofNotZero (fst (sumZeroImpliesZero proofZero))

|||Proof that b != 0 implies a + b != 0
nonZeroSumNotZeroRight :  {a : Nat} -> {b : Nat} -> (Not (b = Z)) -> Not (a + b = Z)
nonZeroSumNotZeroRight {a} {b} proofNotZero proofZero = proofNotZero (snd (sumZeroImpliesZero proofZero))

|||Proof that a != 0 and b != 0 implies a * b ! = 0
nonZeroMultNotZero : {a : Nat} -> {b : Nat} ->
				 (Not (a = Z)) -> (Not (b = Z)) -> (Not (a * b = Z))
nonZeroMultNotZero {a} {b} aNotZ bNotZ proofZero =
	case (multZeroImpliesZero proofZero) of
	(Left aEqZ) => aNotZ aEqZ
	(Right bEqZ) => bNotZ bEqZ

|||Proof that (S a) + b = a + (S b)
plusSymmetricInS : {a : Nat} -> {b : Nat} -> ((S a) + b = a + (S b))
plusSymmetricInS {a = Z} {b} = Refl
plusSymmetricInS {a = S k} {b} = cong (plusSymmetricInS {a = k} {b})

||| Proof that a = c, b = d and a <= b implies c <= d
lteSubstitutes : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
				(LTE a b) -> (a = c) -> (b = d) -> (LTE c d)
lteSubstitutes proofLTE Refl Refl = proofLTE

|||Proof that k < n implies n != 0
gtSuccImpliesNotZ : {k : Nat} -> (n : Nat) -> (LT k n) -> (Not (n = Z))
gtSuccImpliesNotZ {k} n proofLT nIsZ = succNotLTEzero (lteSubstitutes proofLT Refl nIsZ)

notLTEImpliesGTE : {a : Nat} -> {b : Nat} -> (Not (LTE a b)) -> (LTE b a)
notLTEImpliesGTE {a = Z} {b} contra = void (contra (LTEZero))
notLTEImpliesGTE {a = (S k)} {b = Z} contra = LTEZero
notLTEImpliesGTE {a = (S k)} {b = (S j)} contra =
	LTESucc (notLTEImpliesGTE {a = k} {b = j} (\evidence => contra (LTESucc evidence)))

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

|||Proof that a * c != b * c implies a != b
multConstantRightNot : {a : Nat} -> {b : Nat} -> {c : Nat} -> (Not ((a * c) = (b * c))) -> (Not (a = b))
multConstantRightNot {a} {b} {c} proofNotEq proofEq = void (proofNotEq (cong {f = (\n => n * c)} proofEq))

|||Proof that a * c = b * c and c != 0 implies a = b
multRightCancel : (left1 : Nat) -> (left2 : Nat) -> (right : Nat) -> (Not (right = Z)) -> (left1 * right = left2 * right) -> (left1 = left2)
multRightCancel left1 left2 Z rightnotzero prf = void (rightnotzero Refl)
multRightCancel Z Z (S k) rightnotzero prf = Refl
multRightCancel Z (S _) (S _) _ proofEq = void (ZIsNotS proofEq)
multRightCancel (S _) Z (S _) _ proofEq = void (SIsNotZ proofEq)
multRightCancel (S j) (S i) (S k) rightnotzero prf = cong (multRightCancel j i (S k) rightnotzero (plusLeftCancel (S k) (j * (S k)) (i * (S k))  prf))

|||Proof that c * a = c * b and c != 0 implies a = b
multLeftCancel : (left : Nat) -> (right1 : Nat) -> (right2 : Nat) -> (Not (left = Z)) -> (left * right1 = left * right2) -> (right1 = right2)
multLeftCancel left right1 right2 lnotz prf =
	multRightCancel right1 right2 left lnotz
	(rewrite (multCommutative right1 left) in
	rewrite (multCommutative right2 left) in
	prf)

|||Proof that n * a = a and a != 0 implies n = 1
multLeftIdIsOne : {n : Nat} -> {a : Nat} ->
			   (Not (a = Z)) -> (n * a = a) -> (n = 1)
multLeftIdIsOne {n} {a} notZ proofEq = trans (sym (multOneRightNeutral n)) (multRightCancel (n * 1) 1 a notZ (rewrite (sym (multAssociative n 1 a)) in (rewrite (multOneLeftNeutral a) in proofEq)))

|||Proof that (a + k = b) and (b + l = a) implies a = b
plusAntiSymmetric : {a : Nat} -> {b : Nat} -> {k : Nat} -> {l : Nat} ->
					  (a + k = b) -> (b + l = a) -> (a = b)
plusAntiSymmetric {a} {b} {k} {l} proofEqLeft proofEqRight =
	(rewrite (sym (plusZeroRightNeutral a)) in (rewrite (sym (fst (sumZeroImpliesZero (plusLeftCancel a (k + l) Z step)))) in proofEqLeft)) where
		step = trans (rewrite (plusAssociative a k l) in (trans (cong {f = (\n => n + l)} proofEqLeft) proofEqRight)) (sym (plusZeroRightNeutral a))

|||Proof that (a = k * b) and (b = l * a) impplies (a = b)
multAntiSymmetric : {a : Nat} -> {b : Nat} -> {k : Nat} -> {l : Nat} ->
					(a = k * b) -> (b = l * a) -> (a = b)
multAntiSymmetric {a = Z} {b} {k} {l} proofEqLeft proofEqRight = sym (rewrite (sym (multZeroRightZero l)) in proofEqRight)
multAntiSymmetric {a = (S n)} {b} {k} {l} proofEqLeft proofEqRight =
	rewrite (sym (multOneLeftNeutral b)) in
	(trans proofEqLeft (cong {f = (\k => k * b)} (fst (multOneImpliesOne (sym (multRightCancel 1 (k * l) (S n) SIsNotZ (rewrite (sym (multAssociative k l (S n))) in (rewrite (sym proofEqRight) in (rewrite (multOneLeftNeutral (S n)) in proofEqLeft)))))))))
{-
multAntiSymmetric : {a : Nat} -> {b : Nat} -> {k : Nat} -> {l : Nat} ->
					(a * k = b) -> (b * l = a) -> (a = b)
multAntiSymmetric {a = Z} {b} {k} {l} proofEqLeft proofEqRight = proofEqLeft
multAntiSymmetric {a = (S n)} {b} {k} {l} proofEqLeft proofEqRight =
	(rewrite (sym (multOneRightNeutral (S n))) in (trans (cong {f = (\k => (S n) * k)} (sym (fst (multOneImpliesOne (multLeftCancel (S n) (k * l) 1 SIsNotZ step))))) proofEqLeft)) where
		step = trans (rewrite (multAssociative (S n) k l) in (trans (cong {f = (\n => n * l)} proofEqLeft) proofEqRight)) (sym (multOneRightNeutral (S n)))
-}

|||Proof that a = r + q * b implies (n * a) = (n * r) + q * (n * b)
extendEqualMult : {a : Nat} -> {b : Nat} -> {q : Nat} -> {r : Nat} -> (a = r + (q * b)) ->
			   (n : Nat) -> ((n * a) = (n * r) + q * (n * b))
extendEqualMult {a} {b} {q} {r} proofEq n =
	rewrite (multAssociative q n b) in
	rewrite (multCommutative q n) in
	rewrite (sym (multAssociative n q b)) in
	rewrite (sym (multDistributesOverPlusRight n r (q * b))) in
	cong {f = (\l => n * l)} proofEq
