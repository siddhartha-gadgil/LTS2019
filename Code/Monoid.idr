module Monoid

%access public export

||| The proof that some element is identity in the type
total
IsIdentity : (mon : Type) -> ((*) : mon -> mon -> mon) -> (e : mon) -> Type
IsIdentity mon (*) e = (a : mon) -> ((a*e) = a, (e*a) = a)

||| Given a type and a binary operation the type of proofs that the operation is associative
total
Associative : (typ : Type) -> ((*): typ -> typ -> typ) -> Type
Associative typ (*) = (a : typ) -> (b : typ) -> (c : typ) -> ((a * b) * c) = (a * (b * c))

||| Given a type and a binary operation the type of proofs that the operation is commutative
total
Commutative : (typ : Type) -> ((*) : typ -> typ -> typ) -> Type
Commutative typ (*) = (a : typ) -> (b : typ) -> (a * b) = (b * a)

||| Given a type and a binary operation the type of proofs that identity exists
total
IdentityExists : (typ : Type) -> ((*) : typ -> typ -> typ) -> Type
IdentityExists typ (*) = (e : typ ** (IsIdentity typ (*) e))
--((a : typ) -> ((a*e) = a, (e*a) = a)))

total
IsMonoid : (mon : Type) -> ((*) : mon -> mon -> mon) -> Type
IsMonoid mon (*) = (Associative mon (*), IdentityExists mon (*))

||| Gives the identity of the monoid
total
Monoid_id : (mon : Type) -> ((*) : mon -> mon -> mon) -> (IsMonoid mon (*)) 
            -> (IdentityExists mon (*))
Monoid_id mon (*) (pfAss, pfId) = pfId


