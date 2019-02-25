module Order

%default total
%access public export

data InclusiveEither : (typeLeft : Type) -> (typRight : Type) -> Type where
	LeftInc : typLeft -> Not typRight -> InclusiveEither typLeft typRight
	RightInc : Not typLeft -> typRight -> InclusiveEither typLeft typRight
	Both : typLeft -> typRight -> InclusiveEither typLeft typRight

data ExclusiveEither : (typLeft : Type) -> (typRight : Type) -> Type where
	LeftExc : typLeft -> Not typRight -> ExclusiveEither typLeft typRight
	RightExc : Not typLeft -> typRight -> ExclusiveEither typLeft typRight

|||Type of subset of a set
subset : Type -> Type
subset typ = (typ -> Bool)

|||Type of proof that an element x belongs to a subset
isIn : {typ : Type} -> (subset typ) -> (x : typ) -> Type
isIn {typ} subSet x = ((subSet x) = True)

|||Type of proof that two relations are equal
relEqual : {typ : Type} -> (typ -> typ -> Type) -> (typ -> typ -> Type) -> Type
relEqual {typ} r1 r2 = (a : typ) -> (b : typ) -> ((r1 a b) -> (r2 a b), (r2 a b) -> (r1 a b))

|||Induces a strict relation from a relation
toStrictRelation : {typ : Type} -> (r : (typ -> typ -> Type)) -> (typ -> typ -> Type)
toStrictRelation r = (\a => (\b => (r a b, Not (a = b))))

|||Induces a reverse relation from a relation
toReverseRelation : {typ : Type} -> (r : (typ -> typ -> Type)) -> (typ -> typ -> Type)
toReverseRelation r = (\a => (\b => (r b a)))

|||Induces a strict reverse relation from a relation
toStrictReverseRelation : {typ : Type} -> (r : (typ -> typ -> Type)) -> (typ -> typ -> Type)
toStrictReverseRelation r = (\a => (\b => (r b a, Not (b = a))))

|||Type of proof that a relation is reflexive
isReflexive : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isReflexive {typ} r = {a : typ} -> (r a a)

|||Type of proof that a relation is symmetric
isSymmetric : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isSymmetric {typ} r = {a : typ} -> {b : typ} -> (r a b) -> (r b a)

|||Type of proof that a relation is anti-symmetric
isAntiSymmetric : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isAntiSymmetric {typ} r = {a : typ} -> {b : typ} -> (r a b) -> (r b a) -> (a = b)

|||Type of proof that a relation is transitive
isTransitive : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isTransitive {typ} r = {a : typ} -> {b : typ} -> {c : typ} -> (r a b) -> (r b c) -> (r a c)

|||Type of proof that a relation is an equivalence
isEquivalence : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isEquivalence {typ} r = (isReflexive r, isSymmetric r, isTransitive r)

|||Type of proof that a relation is a partial order
isPartialOrder : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isPartialOrder {typ} r = (isReflexive r, isAntiSymmetric r, isTransitive r)

|||Type of proof that a relation is a total order
isTotalOrder : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isTotalOrder {typ} r = (isPartialOrder r, (a : typ) -> (b : typ) -> (InclusiveEither (r a b) ((toReverseRelation r) a b)))

|||Type of proof that a relation is a well-order
isWellOrder : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isWellOrder {typ} r = (isPartialOrder r, (subSet : (subset typ)) -> (a : typ ** (isIn subSet a, ((x : typ) -> (isIn subSet x) -> (r a x)))))

|||Proof that the reverse of the reverse of the relation is the relation
reverseIdempotent : {typ : Type} -> {r : (typ -> typ -> Type)} ->
				(relEqual r (toReverseRelation (toReverseRelation r)))
reverseIdempotent {typ} {r} a b = (id, id)

|||Proof that the reverse of a reflexive relation is reflexive
reversePreservesRefl : {typ : Type} -> {r : (typ -> typ -> Type)} ->
					(isReflexive r) -> (isReflexive (toReverseRelation r))
reversePreservesRefl {typ} {r} rIsRefl = rIsRefl

|||Proof that the reverse of a symmetric relation is symmetric
reversePreservesSymm : {typ : Type} -> {r : (typ -> typ -> Type)} ->
					(isSymmetric r) -> (isSymmetric (toReverseRelation r))
reversePreservesSymm {typ} {r} rIsSymm = rIsSymm

|||Proof that the reverse of an anti-symmetric relation is anti-symmetric
reversePreservesAntiSymm : {typ : Type} -> {r : (typ -> typ -> Type)} ->
						(isAntiSymmetric r) -> (isAntiSymmetric (toReverseRelation r))
reversePreservesAntiSymm {typ} {r} rIsAntiSymm relLeft relRight = rIsAntiSymm relRight relLeft

|||Proof that the reverse of a transitive relation is transitive
reversePreservesTrans : {typ : Type} -> {r : (typ -> typ -> Type)} ->
					(isTransitive r) -> (isTransitive (toReverseRelation r))
reversePreservesTrans {typ} {r} rIsTrans relLeft relRight = rIsTrans relRight relLeft

|||Proof that a reverse order of a symmetric relation is the relation itself
reverseSymmEq : {typ : Type} -> {r : (typ -> typ -> Type)} ->
				(isSymmetric r) -> (relEqual r (toReverseRelation r))
reverseSymmEq {typ} {r} rIsSymmetric a b = (rIsSymmetric, rIsSymmetric)

|||Proof that a reverse order of a partial order is a partial order
reversePOrderIsPOrder : {typ : Type} -> {r : (typ -> typ -> Type)} ->
					(isPartialOrder r) -> (isPartialOrder (toReverseRelation r))
reversePOrderIsPOrder {typ} {r} (rIsRefl, rIsAntiSym, rIsTrans) = (rIsRefl, reversePreservesAntiSymm rIsAntiSym, reversePreservesTrans {typ} {r} rIsTrans)

|||Proof that !(b <= a) implies a != b
notSymmImpliesNotEq : {typ : Type} -> {r : (typ -> typ -> Type)} -> (isReflexive r) -> (Not ((toReverseRelation r) a b)) -> (Not (a = b))
notSymmImpliesNotEq {typ} {r} rIsRefl notLTE Refl = void(notLTE rIsRefl)

|||Proof that a total order leads to a strict order
toStrictOrder : {typ : Type} -> {r : (typ -> typ -> Type)} -> (isTotalOrder r) -> ((a : typ) -> (b : typ) -> (Either (a = b) (ExclusiveEither ((toStrictRelation r) a b) ((toStrictReverseRelation r) a b))))
toStrictOrder {typ} {r} rIsTotalOrder a b =
	case rIsTotalOrder of
	(rIsPartialOrder, rIsTotal) =>
		case (rIsPartialOrder) of
		(rIsRefl, rIsAntiSymm, rIsTrans) =>
				case (rIsTotal a b) of
				(Both leftOrder rightOrder) => Left (rIsAntiSymm leftOrder rightOrder)
				(LeftInc leftOrder notRightOrder) => Right (LeftExc (leftOrder, notSymmImpliesNotEq rIsRefl notRightOrder) (\rightOrder => notRightOrder (fst rightOrder)))
				(RightInc notLeftOrder rightOrder) => Right (RightExc (\leftOrder => notLeftOrder (fst leftOrder)) (rightOrder, notSymmImpliesNotEq rIsRefl notLeftOrder))
