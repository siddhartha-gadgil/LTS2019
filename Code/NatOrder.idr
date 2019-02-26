module NatOrder

import NatUtils
import Order

%default total
%access public export

|||New type for <= on Nat
LEQ : (a : Nat) -> (b : Nat) -> Type
LEQ a b = (k : Nat ** ((a + k) = b))

|||New type for >= on Nat
GEQ : (a : Nat) -> (b : Nat) -> Type
GEQ a b = LEQ b a

|||New type for < on Nat
LNEQ : (a : Nat) -> (b : Nat) -> Type
LNEQ a b = (LEQ a b, Not (a = b))

|||New type for > on Nat
GNEQ : (a : Nat) -> (b : Nat) -> Type
GNEQ a b = LNEQ b a

|||Proof that 0 is the smallest natural number
LEQZero : {n : Nat} -> LEQ Z n
LEQZero {n} = (n ** Refl)

|||Proof that 0 is lesser than every successor
LNEQZeroSucc : {n : Nat} -> LNEQ Z (S n)
LNEQZeroSucc {n} = (((S n) ** Refl), ZIsNotS)

|||Proof that a <= b implies (S a) <= (S b)
LEQSucc : {a : Nat} -> {b : Nat} -> (LEQ a b) -> (LEQ (S a) (S b))
LEQSucc {a} {b} (k ** proofEq) = (k ** cong proofEq)

|||Proof that a < b implies (S a) < (S b)
LNEQSucc : {a : Nat} -> {b : Nat} -> (LNEQ a b) -> (LNEQ (S a) (S b))
LNEQSucc {a} {b} ((k ** proofEq), proofNotEq) = ((k ** cong proofEq), proofNotEqSucc proofNotEq) where
	proofNotEqSucc : (Not (a = b)) -> (Not (S a = S b))
	proofNotEqSucc proofNotEq proofEq = proofNotEq (predEqual proofEq)

|||Proof that (S a) <= (S b) implies a <= b
LEQPred : {a : Nat} -> {b : Nat} -> (LEQ (S a) (S b)) -> (LEQ a b)
LEQPred {a} {b} (k ** proofEq) = (k ** predEqual proofEq)

|||Proof that (S a) < (S b) implies a < b
LNEQPred : {a : Nat} -> {b : Nat} -> (LNEQ (S a) (S b)) -> (LNEQ a b)
LNEQPred {a} {b} ((k ** proofEq), proofNotEq) = ((k ** predEqual proofEq), proofNotEqPred proofNotEq) where
	proofNotEqPred : (Not (S a = S b)) -> (Not (a = b))
	proofNotEqPred proofNotEq proofEq = proofNotEq (cong proofEq)

|||Proof that !(a <= b) implies !((S a) <= (S b))
notLEQSucc : {a : Nat} -> {b : Nat} -> (Not (LEQ a b)) -> (Not (LEQ (S a) (S b)))
notLEQSucc {a} {b} proofNotLEQ proofLEQ = proofNotLEQ (LEQPred proofLEQ)

|||Proof that !((S a) <= (S b)) implies !(a <= b)
notLEQPred : {a : Nat} -> {b : Nat} ->  (Not (LEQ (S a) (S b))) -> (Not (LEQ a b))
notLEQPred {a} {b} proofNotLEQ proofLEQ = proofNotLEQ (LEQSucc proofLEQ)

|||Proof that !(a < b) implies !((S a) < (S b))
notLNEQSucc : {a : Nat} -> {b : Nat} -> (Not (LNEQ a b)) -> (Not (LNEQ (S a) (S b)))
notLNEQSucc {a} {b} proofNotLNEQ proofLNEQ = proofNotLNEQ (LNEQPred proofLNEQ)

|||Proof that !((S a) < (S b)) implies !(a < b)
notLNEQPred : {a : Nat} -> {b : Nat} ->  (Not (LNEQ (S a) (S b))) -> (Not (LNEQ a b))
notLNEQPred {a} {b} proofNotLNEQ proofLNEQ = proofNotLNEQ (LNEQSucc proofLNEQ)

|||Proof that !(a < = b) implies b < a
notLEQImpliesGNEQ : {a : Nat} -> {b : Nat} -> (Not (LEQ a b)) -> (GNEQ a b)
notLEQImpliesGNEQ {a = Z} {b} proofNotLEQ = void (proofNotLEQ (b ** Refl))
notLEQImpliesGNEQ {a = (S n)} {b = Z} _ = ((S n ** Refl), ZIsNotS)
notLEQImpliesGNEQ {a = (S n)} {b = (S m)} proofNotLEQ = (LEQSucc proofGEQ, notEqualSucc proofNotEq) where
	proofGEQ = fst (notLEQImpliesGNEQ {a = n} {b = m} (notLEQPred proofNotLEQ))
	proofNotEq = snd (notLEQImpliesGNEQ {a = n} {b = m} (notLEQPred proofNotLEQ))

|||Proof that !(a < b) implies b <= a
notLNEQImpliesGEQ : {a : Nat} -> {b : Nat} -> (Not (LNEQ a b)) -> (GEQ a b)
notLNEQImpliesGEQ {a} {b = Z} _ = (a ** Refl)
notLNEQImpliesGEQ {a = Z} {b = (S m)} proofNotLNEQ = void (proofNotLNEQ (((S m) ** Refl), ZIsNotS))
notLNEQImpliesGEQ {a = (S n)} {b = (S m)} proofNotLNEQ = (LEQSucc proofGEQ) where
	proofGEQ = notLNEQImpliesGEQ {a = n} {b = m} (notLNEQPred proofNotLNEQ)

|||decides if a <= b
isLEQ : (a : Nat) -> (b : Nat) -> Dec (LEQ a b)
isLEQ Z b = Yes (b ** Refl)
isLEQ (S a) Z = No (\(k ** proofEq) => (SIsNotZ proofEq))
isLEQ (S a) (S b) with (isLEQ a b)
	isLEQ (S a) (S b) | (Yes proofLEQ) = Yes (LEQSucc proofLEQ)
	isLEQ (S a) (S b) | (No contra) = No (\(k ** proofEq) => (contra (k ** (predEqual proofEq))))

|||Proof that a <= b implies a = b or a < b
leqImpliesEqOrLNEQ : {a : Nat} -> {b : Nat} -> (LEQ a b) -> Either (a = b) (LNEQ a b)
leqImpliesEqOrLNEQ {a} {b} (k ** proofEq) = case k of
	Z => Left (rewrite (plusCommutative Z a) in proofEq)
	(S n) => Right (((S n) ** proofEq), nonZeroSumNotEqual proofEq SIsNotZ)

|||Proof that all successors are larger than 0
succNotLEQzero : {n : Nat} -> (Not (LEQ (S n) Z))
succNotLEQzero {n} = \(k ** proofEq) => (SIsNotZ proofEq)

|||Proof that LEQ is reflexive
leqRefl : {n : Nat} -> LEQ n n
leqRefl {n} = (Z ** plusZeroRightNeutral n)

|||Proof that (a + k = b) and (b + l = a) implies (k = 0) and (l = 0)
leqAntiSymmetricIndirect : {a : Nat} -> {b : Nat} ->
						(proofLEQLeft : (LEQ a b)) -> (proofLEQRight : (LEQ b a)) ->
						((fst proofLEQLeft) = Z, (fst proofLEQRight) = Z)
leqAntiSymmetricIndirect {a} {b} (k ** proofEqLeft) (l ** proofEqRight) =
	sumZeroImpliesZero (plusLeftCancel a (k + l) Z inductionStep) where
	inductionStep = rewrite (plusAssociative a Z (k + l)) in
					rewrite (plusZeroRightNeutral a) in
					rewrite (plusAssociative a k l) in
					trans (cong {f = (\n => n + l)} proofEqLeft) proofEqRight

|||Proof that LEQ is antisymmetric
leqAntiSymmetric : {a : Nat} -> {b : Nat} -> (LEQ a b) -> (LEQ b a) -> (a = b)
leqAntiSymmetric {a} {b} (k ** proofEqLeft) (l ** proofEqRight) =
	rewrite (plusCommutative Z a) in
	rewrite (sym (fst (leqAntiSymmetricIndirect {a} {b} (k ** proofEqLeft) (l ** proofEqRight)))) in proofEqLeft

|||Proof that LEQ is transitive
leqTransitive : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LEQ a b) -> (LEQ b c) -> (LEQ a c)
leqTransitive {a} {b} {c} (k ** proofEqLeft) (l ** proofEqRight) = ((k + l) ** proofEq) where
	proofEq = rewrite (plusAssociative a k l) in
			trans (cong {f = (\n => n + l)} proofEqLeft) (proofEqRight)

|||Proof that !(a <= b) and !(b <= a) is impossible
notBothLEQ : {a : Nat} -> {b : Nat} -> (Not (LEQ a b)) -> (Not (LEQ b a)) -> Void
notBothLEQ {a} {b} notaLEQb notbLEQa =
	case (notLEQImpliesGNEQ notaLEQb) of
	(bLEQa, bNotEqa) =>
		case (notLEQImpliesGNEQ notbLEQa) of
		(aLEQb, aNotEqb) =>
			void (aNotEqb (leqAntiSymmetric aLEQb bLEQa))

|||Proof that LEQ is a total order (any two elements are comparable)
leqTotal : {a : Nat} -> {b : Nat} -> InclusiveEither (LEQ a b) (LEQ b a)
leqTotal {a} {b} = case (isLEQ a b) of
				(Yes aLEQb) => case (isLEQ b a) of
							(Yes bLEQa) => (Both aLEQb bLEQa)
							(No bNotLEQa) => (LeftInc aLEQb bNotLEQa)
				(No aNotLEQb) => case (isLEQ b a) of
							(Yes bLEQa) => (RightInc aNotLEQb bLEQa)
							(No bNotLEQa) => void (notBothLEQ aNotLEQb bNotLEQa)

-- leqTotalOrder : isTotalOrder LEQ
-- leqTotalOrder = ((leqRefl, leqAntiSymmetric, leqTransitive), leqTotal)

|||Proof that a <= b implies a <= b + c
leqPlusRight : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LEQ a b) -> (LEQ a (b + c))
leqPlusRight {a} {b} c (k ** proofEq) = ((k + c) ** rewrite (plusAssociative a k c) in (cong {f = (\n => (n + c))} proofEq))

|||Proof that a + c <= b implies a <= b
ltePlusLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LEQ (a + c) b) -> (LEQ a b)
ltePlusLeft {a} {b} {c} (k ** proofEq) = ((c + k) ** rewrite (plusAssociative a c k) in proofEq)

|||Proof that a <= b implies (c + a) <= (c + b)
leqPlusConstantLeft : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LEQ a b) -> (LEQ (c + a) (c + b))
leqPlusConstantLeft {a} {b} c (k ** proofEq) = (k ** proofFinalEq) where
	proofFinalEq = rewrite (sym (plusAssociative c a k)) in (cong {f = (\n => c + n)} proofEq)

|||Proof that a <= b implies (a + c) <= (b + c)
leqPlusConstantRight : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LEQ a b) -> (LEQ (a + c) (b + c))
leqPlusConstantRight {a} {b} c proofLEQ = rewrite (plusCommutative a c) in
									rewrite (plusCommutative b c) in
									(leqPlusConstantLeft c proofLEQ)

|||Proof that (c + a) <= (c + b) implies a <= b
leqMinusConstantLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LEQ (c + a) (c + b)) -> (LEQ a b)
leqMinusConstantLeft {a} {b} {c} (k ** proofEq) = (k ** proofFinalEq) where
	proofFinalEq = (plusLeftCancel c (a + k) b (rewrite (plusAssociative c a k) in proofEq))

|||Proof that (a + c) <= (b + c) implies a <= b
leqMinusConstantRight : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LEQ (a + c) (b + c)) -> (LEQ a b)
leqMinusConstantRight {a} {b} {c} proofLEQ = leqMinusConstantLeft {a} {b} {c} proofFinalEq where
	proofFinalEq = rewrite (plusCommutative c a) in
				rewrite (plusCommutative c b) in proofLEQ

|||Proof that if a <= b, and c <= d, then (a + c) <= (b + d)
leqPlusIsLEQ : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
			(LEQ a b) -> (LEQ c d) -> (LEQ (a + c) (b + d))
leqPlusIsLEQ {a = a0} {b = b0} {c = c0} {d = d0} proofLeftLEQ proofRightLEQ =
	leqTransitive (leqPlusConstantRight {a = a0} {b = b0} c0 proofLeftLEQ) (leqPlusConstantLeft {a = c0} {b = d0} b0 proofRightLEQ)

|||Proof that a <= b implies (c * a) <= (c * b)
leqMultConstantLeft : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LEQ a b) -> (LEQ (c * a) (c * b))
leqMultConstantLeft {a} {b} c (k ** proofEq) = ((c * k) ** proofFinalEq) where
	proofFinalEq = rewrite (sym (multDistributesOverPlusRight c a k)) in
				cong {f = (\n => c * n)} proofEq

|||Proof that a <= b implies (a * c) <= (b * c)
leqMultConstantRight : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LEQ a b) -> (LEQ (a * c) (b * c))
leqMultConstantRight {a} {b} c (k ** proofEq) = ((k * c) ** proofFinalEq) where
	proofFinalEq = rewrite (sym (multDistributesOverPlusLeft a k c)) in
				cong {f = (\n => n * c)} proofEq

|||Proof that if a <= b, and c <= d, then (a * c) <= (b * d)
leqMultIsLEQ : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
			(LEQ a b) -> (LEQ c d) -> (LEQ (a * c) (b * d))
leqMultIsLEQ {a = a0} {b = b0} {c = c0} {d = d0} proofLeftLEQ proofRightLEQ =
	leqTransitive (leqMultConstantRight {a = a0} {b = b0} c0 proofLeftLEQ) (leqMultConstantLeft {a = c0} {b = d0} b0 proofRightLEQ)

|||Proof that (c * a) <= (c * b) and c != 0 implies a <= b
leqDivConstantLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (Not (c = Z)) ->
					(LEQ (c * a) (c * b)) -> (LEQ a b)
--To be proved

|||Proof that (a * c) <= (b * c) and c != 0 implies a <= b
leqDivConstantRight : {a : Nat} -> {b : Nat} -> {c : Nat} -> (Not (c = Z)) ->
					(LEQ (a * c) (b * c)) -> (LEQ a b)
--To be proved

------------------------------------------------------------------------------------------------------

|||Convert from LEQ to LTE
leqToLTE : {a : Nat} -> {b : Nat} -> (LEQ a b) -> (LTE a b)
leqToLTE {a = Z} {b} _ = LTEZero
leqToLTE {a = S m} {b = Z} proofLEQ = void(succNotLEQzero proofLEQ)
leqToLTE {a = S m} {b = S n} (k ** proofEq) = LTESucc (leqToLTE {a = m} {b = n} (k ** predEqual proofEq))

|||Convert from LTE to LEQ
lteToLEQ : {a : Nat} -> {b : Nat} -> (LTE a b) -> (LEQ a b)
lteToLEQ {a = Z} {b} _ = LEQZero
lteToLEQ {a = S m} {b = Z} proofLTE = void(succNotLTEzero proofLTE)
lteToLEQ {a = S m} {b = S n} (LTESucc proofLTE) = LEQSucc (lteToLEQ {a = m} {b = n} proofLTE)

-------------------------------------------------------------------------------------------------------
