module NatOrder

%default total
%access public export

|||Proof that S m = S n implies m = n
predEqual : {a : Nat} -> {b : Nat} -> (S a = S b) -> (a = b)
predEqual {a} {b} proofEq = cong {f = Prelude.Nat.pred} proofEq

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
GNEQ a b = (GEQ a b, Not (a = b))

|||Proof that 0 is the smallest Natural numbers
LEQZero : {n : Nat} -> LEQ Z n
LEQZero {n} = (n ** Refl)

|||Proof that a <= b implies (S a) <= (S b)
LEQSucc : {a : Nat} -> {b : Nat} -> (LEQ a b) -> (LEQ (S a) (S b))
LEQSucc {a} {b} (k ** proofEq) = (k ** cong proofEq)

|||Proof that all successors are larger than 0
succNotLEQzero : {n : Nat} -> (Not (LEQ (S n) Z))
succNotLEQzero {n} = \(k ** proofEq) => (SIsNotZ proofEq)

||| LEQ is reflexive
leqRefl : {n : Nat} -> LEQ n n
leqRefl {n} = (Z ** plusZeroRightNeutral n)

||| Finds (a - b) given b <= a, with proof that b + (a - b) = a
minusWithProof : (a : Nat) -> (b : Nat) -> (LEQ b a) -> (n : Nat ** (b + n = a))
minusWithProof a b (k ** proofEq) = (k ** proofEq)

|||Proof that a <= b implies a <= b + c
leqPlusRight : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LEQ a b) -> (LEQ a (b + c))
leqPlusRight {a} {b} c (k ** proofEq) = ((k + c) ** rewrite (plusAssociative a k c) in (cong {f = (\n => (n + c))} proofEq))

|||Proof that a + c <= b implies a <= b
ltePlusLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LEQ (a + c) b) -> (LEQ a b)
ltePlusLeft {a} {b} {c} (k ** proofEq) = ((c + k) ** rewrite (plusAssociative a c k) in proofEq)

|||Proof that a <= b and b <= c implies a <= c
leqTransitive : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LEQ a b) -> (LEQ b c) -> (LEQ a c)
leqTransitive {a} {b} {c} (k ** proofEqLeft) (l ** proofEqRight) = ((k + l) ** proofEq) where
	proofEq = rewrite (plusAssociative a k l) in
			trans (cong {f = (\n => n + l)} proofEqLeft) (proofEqRight)

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
--to be defined


|||Proof that (a * c) <= (b * c) and c != 0 implies a <= b
leqDivConstantRight : {a : Nat} -> {b : Nat} -> {c : Nat} -> (Not (c = Z)) ->
					(LEQ (a * c) (b * c)) -> (LEQ a b)
--to be defined

------------------------------------------------------------------------------------------------------

|||decides if a <= b
isLEQ : (a : Nat) -> (b : Nat) -> Dec (LEQ a b)
isLEQ Z b = Yes (b ** Refl)
isLEQ (S a) Z = No (\(k ** proofEq) => (SIsNotZ proofEq))
isLEQ (S a) (S b) with (isLEQ a b)
	isLEQ (S a) (S b) | (Yes proofLEQ) = Yes (LEQSucc proofLEQ)
	isLEQ (S a) (S b) | (No contra) = No (\(k ** proofEq) => (contra (k ** (predEqual proofEq))))

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
