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

||| The type of proofs that a function between groups is a group homomorphism
total
Hom: (grp : Type) -> ((*) : grp -> grp -> grp) -> (IsGroup grp (*)) ->
     (g : Type) -> ((+) : g -> g -> g) -> (IsGroup g (+)) ->
     (f : grp -> g) -> Type
Hom grp (*) pf1 g (+) pf2 f  = ((IsIdentity g (+) e) , (
                               (a : grp) -> (b : grp) -> ((f (a*b)) = ((f a) + (f b))))) where
                               e = f(fst (Group_id grp (*) pf1))

||| The type of proofs that a given group is a subgroup of another, via injective homorphisms
total
Subgroup: (h: Type) -> ((+) : h -> h -> h) -> (IsGroup h (+)) ->
          (g: Type) -> ((*) : g -> g -> g) -> (IsGroup g (*)) -> Type
Subgroup h (+) pfh g (*) pfg = ( f : (h -> g) **
                               (Hom h (+) pfh g (*) pfg f , Inj h g f))
--- DPair (h->g) (\f => ((Hom h (+) pfh g (*) pfg f), (Inj h g f)))

||| The type of proofs that a given subgroup is normal/self-conjugate
total
NSub: (h: Type) -> ((+) : h -> h -> h) -> (pfh: IsGroup h (+)) ->
      (g: Type) -> ((*) : g -> g -> g) -> (pfg: IsGroup g (*)) ->
      (Subgroup h (+) pfh g (*) pfg) -> Type
NSub h (+) pfh g (*) pfg (f ** pff) = (a : h) -> (b : g) -> (x : h ** (b*(f a)*(inv b) = (f x))) where
     inv = Inv g (*) pfg
     
--The type of proofs that a type trav traverses a given coset only once, if at all
CosetInj: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (f: trav -> g) -> Type
CosetInj  h (+) pf1 g (*) pf2 sbgrp trav f = ((x: trav) -> (y: trav) -> (p: h ** (f x) = (incl p)*(f y)) -> (x = y)) where
  incl = (fst sbgrp)

--The type of proofs that a type trav traverses every coset of a given group g wrt a subgroup h
CosetAll: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (f: trav -> g) -> Type
CosetAll h (+) pf1 g (*) pf2 sbgrp trav f = ((a: g) -> (p: h ** (t: trav ** ((f t)*(incl p) = a)))) where
  incl = (fst sbgrp)

-- Traversal type - the type of proofs that a given type traverses each coset exactly once
IsTraversal: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> Type
IsTraversal h (+) pf1 g (*) pf2 sbgrp trav = DPair (trav -> g) (\f => (CosetInj h (+) pf1 g (*) pf2 sbgrp trav f, CosetAll h (+) pf1 g (*) pf2 sbgrp trav f))

--Defining the multiplication operation between elements of a traversal
MulTrav: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (IsTraversal h (+) pf1 g (*) pf2 sbgrp trav) -> trav -> trav -> trav
MulTrav h (+) pf1 g (*) pf2 sbgrp trav pftrav y z = (fst (snd ((snd (snd pftrav)) ((f y)*(f z))))) where
  f: trav -> g
  f = (fst pftrav)
  
--Proof of uniqueness of the coset representative in trav, in the following sense
--Proof that the operation that generates coset representative in trav for an element of g (from CosetAll) inverts the function generating a coset representative by going from trav to g (from IsTraversal)
corepfinv: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (pftrav: IsTraversal h (+) pf1 g (*) pf2 sbgrp trav) -> (y: trav) -> (((fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) )) ) = y)
corepfinv h (+) pf1 g (*) pf2 sbgrp trav pftrav y = (sym ((fst (snd pftrav)) y t (p ** (sym (snd (snd  ((snd (snd pftrav)) (f y)) )))) )) where
  t: trav
  t = (fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) ))
  f: trav -> g
  f = (fst pftrav)
  p: h
  p = (fst ((snd (snd pftrav)) (f y)))
