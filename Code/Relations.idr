module Relations

import congruence

%access public export

%default total

data addRel : (ty : Type) -> (ty -> ty -> Type) -> (ty -> ty -> Type) -> (ty -> ty -> Type) where

    inc_l : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
            (a, b : ty) -> (r1 a b) -> (addRel ty r1 r2 a b)

    inc_r : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
            (a, b : ty) -> (r2 a b) -> (addRel ty r1 r2 a b)

    inc_refl : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
               (a : ty) -> (addRel ty r1 r2 a a)

    inc_sym : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
              (a, b : ty) -> (addRel ty r1 r2 a b) -> (addRel ty r1 r2 b a)

    inc_trans : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
                (a, b, c : ty) -> (addRel ty r1 r2 a b) -> (addRel ty r1 r2 b c) ->
                (addRel ty r1 r2 a c)

f : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) -> (a, b : ty) ->
    (addRel ty r1 r2 a b) -> (addRel ty r2 r1 a b)

f ty r1 r2 a b (inc_l ty r1 r2 a b pf) = (inc_r ty r2 r1 a b pf)
f ty r1 r2 a b (inc_r ty r1 r2 a b pf) = (inc_l ty r2 r1 a b pf)
f ty r1 r2 a a (inc_refl ty r1 r2 a) = (inc_refl ty r2 r1 a)
f ty r1 r2 b a (inc_sym ty r1 r2 a b pf) = (inc_sym ty r2 r1 a b (f ty r1 r2 a b pf))
f ty r1 r2 a c (inc_trans ty r1 r2 a b c pfab pfbc) =
    (inc_trans ty r2 r1 a b c (f ty r1 r2 a b pfab) (f ty r1 r2 b c pfbc))

rel_property_1 : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
                 (a, b : ty) -> (pf : (addRel ty r1 r2 a b)) ->
                 ( (f ty r2 r1 a b (f ty r1 r2 a b pf)) = pf)

rel_property_1 ty r1 r2 a b (inc_l ty r1 r2 a b pf) = Refl
rel_property_1 ty r1 r2 a b (inc_r ty r1 r2 a b pf) = Refl
rel_property_1 ty r1 r2 b b (inc_refl ty r1 r2 b) = Refl
rel_property_1 ty r1 r2 a b (inc_sym ty r1 r2 b a pf) = let
    pf1 = rel_property_1 ty r1 r2 b a pf
    pf2 = congruence (addRel ty r1 r2 b a) (addRel ty r1 r2 a b)
        (f ty r2 r1 b a (f ty r1 r2 b a pf)) pf
        (inc_sym ty r1 r2 b a) pf1
    in
    pf2
rel_property_1 ty r1 r2 a c (inc_trans ty r1 r2 a b c pfab pfbc) = ?rhs_5
