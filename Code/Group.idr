module Group

import Monoid
%access public export

||| The proof that b is inverse of a
total
IsInverse : (typ : Type) -> ((*) : typ -> typ -> typ) -> (IdentityExists typ (*)) -> (a : typ) -> (b : typ) -> Type
IsInverse typ (*) pfid a b = ((a*b = fst(pfid)),(b*a = fst(pfid)))

||| Given a type and a binary operation the type of proofs that each element has its inverse
total
InverseExists : (typ : Type) -> ((*) : typ -> typ -> typ) -> Type
InverseExists typ (*) = (pfid : (IdentityExists typ (*)) ** ((a : typ) -> (a_inv ** (IsInverse typ (*) pfid a a_inv))))
--(pfid : (IdentityExists typ (*)) ** ((a : typ) -> (a_inv : typ ** ((a*a_inv = fst(pfid)),(a_inv*a = fst(pfid))))))

||| Given a type and a binary operation the type of proofs that the type along with the
||| operation is a group
total
IsGroup : (grp : Type) -> ((*) : grp -> grp -> grp) -> Type
IsGroup grp (*) = (Associative grp (*), (IdentityExists grp (*), InverseExists grp (*)))

||| Given a group gives it's identity with proof
total
Group_id : (grp : Type) -> ((*) : grp -> grp -> grp) -> (IsGroup grp (*)) -> (IdentityExists grp (*))
Group_id grp (*) pfgrp = (fst (snd pfgrp))

||| Generates inverses with proofs
total
Inv_with_pf : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) -> (x : grp)
              -> (y : grp ** (IsInverse grp (*) (fst (snd (snd pfgrp))) x y))
Inv_with_pf grp (*) pfgrp x = (snd (snd (snd pfgrp))) x

||| Generates inverses
total
Inv: (grp : Type) -> ((*) : grp -> grp -> grp) -> IsGroup grp (*) -> (x: grp) -> grp
Inv grp (*) pf x = fst (Inv_with_pf grp (*) pf x)
-- fst(snd(snd(snd(pf))) x)

||| Given a group, the type of proofs that it is abelian
total
IsAbelianGrp:  (grp : Type) -> ((*) : grp -> grp -> grp) -> Type
IsAbelianGrp grp (*)  = (IsGroup grp (*), Commutative grp (*))
--- (a:grp) -> (b:grp) -> (a*b = b*a)

||| The type of proofs that a given function f between x and y is injective
total
Inj: (x: Type) -> (y: Type) -> (f: x-> y) -> Type
Inj x y f = (a : x) -> (b : x) -> (f a = f b) -> (a = b)

|||The Group data type, with a single constructor
data Group: (g: Type) -> Type where
  MkGroup: (grp : Type) -> ((*) : grp -> grp -> grp) -> (IsGroup grp (*))  -> Group grp

||| The type of proofs that a function between groups is a group homomorphism
total
Hom: (grp : Type) -> Group grp -> (g: Type) -> Group g -> (f : grp -> g) -> Type
Hom grp (MkGroup grp (*) pf1) g (MkGroup g (+) pf2) f  = ((IsIdentity g (+) e) , (
                               (a : grp) -> (b : grp) -> ((f (a*b)) = ((f a) + (f b))))) where
                               e = f(fst (Group_id grp (*) pf1))

||| The type of proofs that a given group is a subgroup of another, via injective homorphisms
total
Subgroup: (h: Type) -> Group h -> (g: Type) -> Group g -> Type
Subgroup h pfh g pfg = DPair (h -> g) (\f => (Hom h pfh g pfg f , Inj h g f))
--- DPair (h->g) (\f => ((Hom h (+) pfh g (*) pfg f), (Inj h g f)))

||| The type of proofs that a given subgroup is normal/self-conjugate
total
NSub: (h: Type) -> (pfh: Group h) -> (g: Type) -> (pfg: Group g) ->
      (Subgroup h pfh g pfg) -> Type
NSub  h (MkGroup h (+) pfh) g (MkGroup g (*) pfg) (f ** pff) = (a : h) -> (b : g) -> (x : h ** (b*(f a)*(inv b) = (f x))) where
     inv = Inv g (*) pfg
