module Relations

import congruence

%access public export

%default total

||| Composing two relations and then extend them to the smallest equivalence relation containing them

data AddRel : (ty : Type) -> (ty -> ty -> Type) -> (ty -> ty -> Type) -> (ty -> ty -> Type) where

    Inc_l : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
            (a, b : ty) -> (r1 a b) -> (AddRel ty r1 r2 a b)

    Inc_r : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
            (a, b : ty) -> (r2 a b) -> (AddRel ty r1 r2 a b)

    Inc_refl : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
               (a : ty) -> (AddRel ty r1 r2 a a)

    Inc_sym : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
              (a, b : ty) -> (AddRel ty r1 r2 a b) -> (AddRel ty r1 r2 b a)

    Inc_trans : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
                (a, b, c : ty) -> (AddRel ty r1 r2 a b) -> (AddRel ty r1 r2 b c) ->
                (AddRel ty r1 r2 a c)

||| A proof that the composition operation is commutative

f : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) -> (a, b : ty) ->
    (AddRel ty r1 r2 a b) -> (AddRel ty r2 r1 a b)

f ty r1 r2 a b (Inc_l ty r1 r2 a b pf) = (Inc_r ty r2 r1 a b pf)
f ty r1 r2 a b (Inc_r ty r1 r2 a b pf) = (Inc_l ty r2 r1 a b pf)
f ty r1 r2 a a (Inc_refl ty r1 r2 a) = (Inc_refl ty r2 r1 a)
f ty r1 r2 b a (Inc_sym ty r1 r2 a b pf) = (Inc_sym ty r2 r1 a b (f ty r1 r2 a b pf))
f ty r1 r2 a c (Inc_trans ty r1 r2 a b c pfab pfbc) =
    (Inc_trans ty r2 r1 a b c (f ty r1 r2 a b pfab) (f ty r1 r2 b c pfbc))

||| Proof that f is the inverse of itself

rel_property_1 : (ty : Type) -> (r1, r2 : (ty -> ty -> Type)) ->
                 (a, b : ty) -> (pf : (AddRel ty r1 r2 a b)) ->
                 ( (f ty r2 r1 a b (f ty r1 r2 a b pf)) = pf)

rel_property_1 ty r1 r2 a b (Inc_l ty r1 r2 a b pf) = Refl
rel_property_1 ty r1 r2 a b (Inc_r ty r1 r2 a b pf) = Refl
rel_property_1 ty r1 r2 b b (Inc_refl ty r1 r2 b) = Refl
rel_property_1 ty r1 r2 a b (Inc_sym ty r1 r2 b a pf) = let
    pf1 = rel_property_1 ty r1 r2 b a pf
    pf2 = congruence (AddRel ty r1 r2 b a) (AddRel ty r1 r2 a b)
        (f ty r2 r1 b a (f ty r1 r2 b a pf)) pf
        (Inc_sym ty r1 r2 b a) pf1
    in
    pf2

rel_property_1 ty r1 r2 a c (Inc_trans ty r1 r2 a b c pfab pfbc) = let
    
    pf1 = rel_property_1 ty r1 r2 a b pfab
    pf2 = rel_property_1 ty r1 r2 b c pfbc
    
    pf3 = congruence (AddRel ty r1 r2 b c) (AddRel ty r1 r2 a c) 
        (f ty r2 r1 b c (f ty r1 r2 b c pfbc)) pfbc (\k => Inc_trans ty r1 r2 a b c pfab k) pf2

    pf4 = congruence (AddRel ty r1 r2 a b) (AddRel ty r1 r2 a c) 
        (f ty r2 r1 a b (f ty r1 r2 a b pfab)) pfab (\k => Inc_trans ty r1 r2 a b c k (f ty r2 r1 b c (f ty r1 r2 b c pfbc))) pf1


    in
    (trans pf4 pf3)
    
    
    
    
    
    
    
    
    
