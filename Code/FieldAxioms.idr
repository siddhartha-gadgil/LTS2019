module FieldAxioms

import ZZ
import ZZUtils
import GCDZZ
import Divisors
import Rationals

%default total

-- The field axioms which require the custom equality EqRat type are verified here.

EqRatAddInvLeft: (x: ZZPair) -> (a: NotZero (snd x))
-> (EqRat (AddRationals x a (AddInverse x a) (xAndInverseNotZeroPlus x a)) (productNonZero a (xAndInverseNotZeroPlus x a)) ((Pos 0), (snd x)*(snd x)) (productNonZero a a))
EqRatAddInvLeft x a = eqMeansEqRat (AddRationals x a (AddInverse x a) (xAndInverseNotZeroPlus x a)) (productNonZero a (xAndInverseNotZeroPlus x a)) ((Pos 0), (snd x)*(snd x)) (productNonZero a a) (addInverseLeft x a)

EqRatAddInvRight: (x: ZZPair) -> (a: NotZero (snd x))
-> (EqRat (AddRationals (AddInverse x a) (xAndInverseNotZeroPlus x a) x a) (productNonZero a (xAndInverseNotZeroPlus x a)) ((Pos 0), (snd x)*(snd x)) (productNonZero a a))
EqRatAddInvRight x a = eqMeansEqRat (AddRationals (AddInverse x a) (xAndInverseNotZeroPlus x a) x a) (productNonZero a (xAndInverseNotZeroPlus x a)) ((Pos 0), (snd x)*(snd x)) (productNonZero a a) (addInverseRight x a)

EqRatMultInvLeft: (x: ZZPair) -> (a: NotZero (fst x)) -> (b: NotZero (snd x))
-> (EqRat (MultiplyRationals x b (MultInverse x a b) (xAndInverseNotZeroMult x a b)) (productNonZero b (xAndInverseNotZeroMult x a b)) ((fst x)*(snd x), (fst x)*(snd x)) (productNonZero a b))
EqRatMultInvLeft x a b = eqMeansEqRat (MultiplyRationals x b (MultInverse x a b) (xAndInverseNotZeroMult x a b)) (productNonZero b (xAndInverseNotZeroMult x a b)) ((fst x)*(snd x), (fst x)*(snd x)) (productNonZero a b) (multInverseLeft x a b)

EqRatMultInvRight: (x: ZZPair) -> (a: NotZero (fst x)) -> (b: NotZero (snd x))
-> (EqRat (MultiplyRationals (MultInverse x a b) (xAndInverseNotZeroMult x a b) x b) (productNonZero (xAndInverseNotZeroMult x a b) b) ((snd x)*(fst x), (snd x)*(fst x)) (productNonZero b a))
EqRatMultInvRight x a b = eqMeansEqRat (MultiplyRationals (MultInverse x a b) (xAndInverseNotZeroMult x a b) x b) (productNonZero (xAndInverseNotZeroMult x a b) b) ((snd x)*(fst x), (snd x)*(fst x)) (productNonZero b a) (multInverseRight x a b)

-- All of the following proofs involve the use of EqRat and its associated properties which are
-- reflexvity, symmetry, transitivity, and the fact that two elements being equal is enough to construct
-- an element of EqRat.

|||Constructs an equality between (a,b) + (c,d) and (c,d) + (a,b)
plusCommQEqRat: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) ->
(EqRat (AddRationals x a y b) (productNonZero a b) (AddRationals y b x a) (productNonZero b a))
plusCommQEqRat x a y b = eqMeansEqRat (AddRationals x a y b) (productNonZero a b) (AddRationals y b x a) (productNonZero b a) (plusCommutativeQ x a y b)

|||Constructs an equality between (a,b)*(c,d) and (c,d)*(a,b)
multCommQEqRat: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) ->
(EqRat (MultiplyRationals x a y b) (productNonZero a b) (MultiplyRationals y b x a) (productNonZero b a))
multCommQEqRat x a y b = eqMeansEqRat (MultiplyRationals x a y b) (productNonZero a b) (MultiplyRationals y b x a) (productNonZero b a) (multCommutativeQ x a y b)

|||Constructs an equality between (a,b) + (0,1) and (a,b).
addIdRightEqRat: (x: ZZPair) -> (a: NotZero (snd x)) ->
(EqRat (AddRationals x a (0,1) PositiveZ) (productNonZero a (PositiveZ)) x a)
addIdRightEqRat x a = eqMeansEqRat (AddRationals x a (0,1) PositiveZ) (productNonZero a (PositiveZ)) (x) (a) (zeroAddIdentityRight x a)

|||Constructs an equality between (a,b) and (a,b) + (0,1).
addIdLeftEqRat: (x: ZZPair) -> (a: NotZero (snd x)) ->
(EqRat (AddRationals (0,1) PositiveZ x a) (productNonZero (PositiveZ) a) x a)
addIdLeftEqRat x a = eqMeansEqRat (AddRationals (0,1) PositiveZ x a) (productNonZero (PositiveZ) a) (x) (a) (zeroAddIdentityLeft x a)

|||Constructs an equality between (a,b)*(1,1) and (a,b).
multIdRightEqRat: (x: ZZPair) -> (a: NotZero (snd x)) ->
(EqRat (MultiplyRationals x a (1,1) PositiveZ) (productNonZero a (PositiveZ)) x a)
multIdRightEqRat x a = eqMeansEqRat (MultiplyRationals x a (1,1) PositiveZ) (productNonZero a (PositiveZ)) (x) (a) (oneMultIdentityRight x a)

|||Constructs an equality between (a,b)*(1,1) and (a,b).
multIdLeftEqRat: (x: ZZPair) -> (a: NotZero (snd x)) ->
(EqRat (MultiplyRationals (1,1) PositiveZ x a) (productNonZero (PositiveZ) a) x a)
multIdLeftEqRat x a = eqMeansEqRat (MultiplyRationals (1,1) PositiveZ x a) (productNonZero (PositiveZ) a) (x) (a) (oneMultIdentityLeft x a)

|||Constructs an equality between ((a,b)+(-a,b)) and 0.
addInverseLeftEqRat: (x: ZZPair) -> (a: NotZero (snd x)) ->
(EqRat (AddRationals x a (AddInverse x a) (xAndInverseNotZeroPlus x a) ) (productNonZero a (xAndInverseNotZeroPlus x a)) (0,1) PositiveZ)
addInverseLeftEqRat x a = EqRatTrans (AddRationals x a (AddInverse x a) (xAndInverseNotZeroPlus x a)) (productNonZero a (xAndInverseNotZeroPlus x a)) ((Pos 0), (snd x)*(snd x)) (productNonZero a a) (0,1) (PositiveZ) (EqRatAddInvLeft x a) (reducedFormZeroRight ((snd x)*(snd x)) (productNonZero a a))

|||Constructs an equality between 0 and ((a,b)+(-a,b)).
addInverseRightEqRat: (x: ZZPair) -> (a: NotZero (snd x)) ->
(EqRat (AddRationals (AddInverse x a) (xAndInverseNotZeroPlus x a) x a) (productNonZero a (xAndInverseNotZeroPlus x a)) (0,1) PositiveZ)
addInverseRightEqRat x a = EqRatTrans (AddRationals (AddInverse x a) (xAndInverseNotZeroPlus x a) x a) (productNonZero a (xAndInverseNotZeroPlus x a)) ((Pos 0), (snd x)*(snd x)) (productNonZero a a) (0,1) (PositiveZ) (EqRatAddInvRight x a) (reducedFormZeroRight ((snd x)*(snd x)) (productNonZero a a))

|||Constructs an equality between (a,b)*(b,a) and (1,1).
multInverseLeftEqRat: (x: ZZPair) -> (a: NotZero (fst x)) -> (b: NotZero (snd x)) ->
(EqRat (MultiplyRationals x b (MultInverse x a b) (xAndInverseNotZeroMult x a b)) (productNonZero b (xAndInverseNotZeroMult x a b)) (1,1) (PositiveZ))
multInverseLeftEqRat x a b = EqRatTrans (MultiplyRationals x b (MultInverse x a b) (xAndInverseNotZeroMult x a b)) (productNonZero b (xAndInverseNotZeroMult x a b)) ((fst x)*(snd x), (fst x)*(snd x)) (productNonZero a b) (1,1) (PositiveZ) (EqRatMultInvLeft x a b) (reducedFormOneRight ((fst x)*(snd x)) (productNonZero a b))

|||Constructs an equality between (1,1) and (a,b)*(b,a).
multInverseRightEqRat: (x: ZZPair) -> (a: NotZero (fst x)) -> (b: NotZero (snd x)) ->
(EqRat (MultiplyRationals (MultInverse x a b) (xAndInverseNotZeroMult x a b) x b) (productNonZero (xAndInverseNotZeroMult x a b) b) (1,1) (PositiveZ))
multInverseRightEqRat x a b = EqRatTrans (MultiplyRationals (MultInverse x a b) (xAndInverseNotZeroMult x a b) x b) (productNonZero (xAndInverseNotZeroMult x a b) b) ((snd x)*(fst x), (snd x)*(fst x)) (productNonZero b a) (1,1) (PositiveZ) (EqRatMultInvRight x a b) (reducedFormOneRight ((snd x)*(fst x)) (productNonZero b a))

|||Constructs an EqRat element of associativity for addition.
plusAssocQEqRat: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (z: ZZPair) -> (c: NotZero (snd z)) ->
(EqRat (AddRationals (AddRationals x a y b) (productNonZero a b) z c) (productNonZero (productNonZero a b) c) (AddRationals x a (AddRationals y b z c) (productNonZero b c)) (productNonZero a (productNonZero b c)))
plusAssocQEqRat x a y b z c = eqMeansEqRat (AddRationals (AddRationals x a y b) (productNonZero a b) z c) (productNonZero (productNonZero a b) c) (AddRationals x a (AddRationals y b z c) (productNonZero b c)) (productNonZero a (productNonZero b c)) (plusAssociativeQ x a y b z c)

|||Constructs an EqRat element of associativity for multiplication.
multAssocQEqRat: (x: ZZPair) -> (a: NotZero (snd x)) -> (y: ZZPair) -> (b: NotZero (snd y)) -> (z: ZZPair) -> (c: NotZero (snd z)) ->
(EqRat (MultiplyRationals (MultiplyRationals x a y b) (productNonZero a b) z c) (productNonZero (productNonZero a b) c) (MultiplyRationals x a (MultiplyRationals y b z c) (productNonZero b c)) (productNonZero a (productNonZero b c)))
multAssocQEqRat x a y b z c = eqMeansEqRat (MultiplyRationals (MultiplyRationals x a y b) (productNonZero a b) z c) (productNonZero (productNonZero a b) c) (MultiplyRationals x a (MultiplyRationals y b z c) (productNonZero b c)) (productNonZero a (productNonZero b c)) (multAssociativeQ x a y b z c)
