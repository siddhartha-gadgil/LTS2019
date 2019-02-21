module Order

data InclusiveEither : (typeLeft : Type) -> (typRight : Type) -> Type where
	OnlyLeft : typLeft -> Not typRight -> InclusiveEither typLeft typRight
	OnlyRight : Not typLeft -> typRight -> InclusiveEither typLeft typRight
	Both : typLeft -> typRight -> InclusiveEither typLeft typRight

|||Type of proof that a relation is reflexive
isReflexive : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isReflexive {typ} r = (a : typ) -> (r a a)

|||Type of proof that a relation is symmetric
isSymmetric : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isSymmetric {typ} r = (a : typ) -> (b : typ) -> (r a b) -> (r b a)

|||Type of proof that a relation is anti-symmetric
isAntiSymmetric : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isAntiSymmetric {typ} r = (a : typ) -> (b : typ) -> (r a b) -> (r b a) -> (a = b)

|||Type of proof that a relation is transitive
isTransitive : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isTransitive {typ} r = (a : typ) -> (b : typ) -> (c : typ) -> (r a b) -> (r b c) -> (r a c)

|||Type of proof that a relation is an equivalence
isEquivalence : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isEquivalence {typ} r = (isReflexive r, isSymmetric r, isTransitive r)

|||Type of proof that a relation is a partial order
isPartialOrder : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isPartialOrder {typ} r = (isReflexive r, isAntiSymmetric r, isTransitive r)

|||Type of proof that a relation is a total order
isTotalOrder : {typ : Type} -> (r : (typ -> typ -> Type)) -> Type
isTotalOrder {typ} r = (isPartialOrder r, (a : typ) -> (b : typ) -> (InclusiveEither (r a b) (r b a)))
