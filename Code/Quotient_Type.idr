module Quotient_Type

%access public export
%default total

IsRefl : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsRefl typ rel = (a : typ) -> (rel a a)

IsSym : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsSym typ rel = (a, b : typ) -> (rel a b) -> (rel b a)

IsTrans : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsTrans typ rel = (a, b, c : typ) -> (rel a b) -> (rel b c) -> (rel a c)

IsEqRel : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsEqRel typ rel = ( (IsRefl typ rel) , ( (IsSym typ rel), (IsTrans typ rel) ) )

data Quotient_Type : (typ : Type) -> (rel : typ -> typ -> Type) -> Type where
    Cons_quotient_Type : (IsEqRel typ rel) -> (Quotient_Type typ rel)

||| Type of proof that a function passes through the relations

Passes_Through : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) ->
                 (ty2 : Type) -> (rel_2 : ty2 -> ty2 -> Type) ->
                 (f : ty1 -> ty2) -> Type

Passes_Through ty1 rel_1 ty2 rel_2 f =
    (a, b : ty1) -> (rel_1 a b) -> (rel_2 (f a) (f b))

||| Type of function between two quotient types
data Quotient_Function : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) ->
                         (ty2 : Type) -> (rel_2 : ty2 -> ty2 -> Type) -> Type where

    Cons_quotient_Function : (f : ty1 -> ty2) -> (Passes_Through ty1 rel_1 ty2 rel_2 f)
        -> (Quotient_Function ty1 rel_1 ty2 rel_2)

||| The type of transports of a relation
Transport_of : (ty : Type) -> (rel : ty -> ty -> Type) -> (P : ty -> Type) -> Type
Transport_of ty rel P = (a, b : ty) -> (rel a b) -> (P a) -> (P b)

||| Definition of a family of quotient types
data Quotient_Family : (ty : Type) -> (rel : ty -> ty -> Type) -> Type where
    Cons_quotient_Family : (P : ty -> Type) -> (Transport_of ty rel P) -> (Quotient_Family ty rel)

||| Given a quotient family gets the underlying family.
get_Family : (ty : Type) -> (rel : ty -> ty -> Type) -> (P : (Quotient_Family ty rel)) ->
             (ty -> Type)
get_Family ty rel (Cons_quotient_Family p tr) = p

||| Given a quotient type gets the transport
get_Transport : (ty : Type) -> (rel : ty -> ty -> Type) -> (P : (Quotient_Family ty rel)) ->
                (Transport_of ty rel (get_Family ty rel P))
get_Transport ty rel (Cons_quotient_Family P tr) = tr

||| Type of proofs that a dependent function passes through the corresponding relations
Passes_Through_Dependent : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) ->
                           (P : (Quotient_Family ty1 rel_1)) ->
                           (relP : (a : ty1) -> ((get_Family ty1 rel_1 P) a) -> ((get_Family ty1 rel_1 P) a) -> Type) ->
                           (f : (a : ty1) -> ((get_Family ty1 rel_1 P) a) ) -> Type

Passes_Through_Dependent ty1 rel_1 P relP f = (a, b : ty1) -> (pt : rel_1 a b) ->
    ( (relP b) ((get_Transport ty1 rel_1 P) a b pt (f a)) (f b))

||| A proof that any equivalence relation factors through equality
EqRel_factors_through_Eq : (ty : Type) -> (rel : ty -> ty -> Type) -> (IsEqRel ty rel) ->
                           (a, b : ty) -> (a = b) -> (rel a b)

EqRel_factors_through_Eq ty rel pfEqRel a a Refl = (fst pfEqRel) a

||| The condition on the function type A -> B to make it the quotient function type (A, relA) -> (B, relB)
Function_rel : (ty1 : Type) -> (rel1 : ty1 -> ty1 -> Type) -> (IsEqRel ty1 rel1) ->
               (ty2 : Type) -> (rel2 : ty2 -> ty2 -> Type) -> (IsEqRel ty2 rel2) ->
               (f, g : (ty1 -> ty2)) ->
               (Passes_Through ty1 rel1 ty2 rel2 f) ->
               (Passes_Through ty1 rel1 ty2 rel2 g) -> Type

Function_rel ty1 rel1 pfEq1 ty2 rel2 pfEq2 f g pf_f pf_g =
      (a, b : ty1) -> (rel1 a b) -> (rel2 (f a) (g b))

IsRefl_Function_rel : (ty1 : Type) -> (rel1 : ty1 -> ty1 -> Type) -> (pf1 : IsEqRel ty1 rel1) ->
                      (ty2 : Type) -> (rel2 : ty2 -> ty2 -> Type) -> (pf2 : IsEqRel ty2 rel2) ->
                      (f : (ty1 -> ty2)) -> (pf_f : Passes_Through ty1 rel1 ty2 rel2 f) ->
                      (Function_rel ty1 rel1 pf1 ty2 rel2 pf2 f f pf_f pf_f)

IsRefl_Function_rel ty1 rel1 pf1 ty2 rel2 pf2 f pf_f = pf_f

IsSym_Function_rel : (ty1 : Type) -> (rel1 : ty1 -> ty1 -> Type) -> (pf1 : IsEqRel ty1 rel1) ->
                     (ty2 : Type) -> (rel2 : ty2 -> ty2 -> Type) -> (pf2 : IsEqRel ty2 rel2) ->
                     (f : (ty1 -> ty2)) -> (pf_f : Passes_Through ty1 rel1 ty2 rel2 f) ->
                     (g : (ty1 -> ty2)) -> (pf_g : Passes_Through ty1 rel1 ty2 rel2 g) ->
                     (Function_rel ty1 rel1 pf1 ty2 rel2 pf2 f g pf_f pf_g) ->
                     (Function_rel ty1 rel1 pf1 ty2 rel2 pf2 g f pf_g pf_f)

IsSym_Function_rel ty1 rel1 pf1 ty2 rel2 pf2 f pf_f g pf_g pf_rel a b pfab = let

    pf_sym_1 : ((a1 : ty1) -> (b1 : ty1) -> (rel1 a1 b1) -> (rel1 b1 a1))
        = (fst (snd pf1))

    pf_sym_2 : ((a1 : ty2) -> (b1 : ty2) -> (rel2 a1 b1) -> (rel2 b1 a1))
        = (fst (snd pf2))

    pf4 : (rel1 b a)
        = pf_sym_1 a b pfab

    pf5 : (rel2 (f b) (g a))
        = pf_rel b a pf4

    pf6 : (rel2 (g a) (f b))
        = pf_sym_2 (f b) (g a) pf5
    in
    pf6

IsTrans_Function_rel : (ty1 : Type) -> (rel1 : ty1 -> ty1 -> Type) -> (pf1 : IsEqRel ty1 rel1) ->
                       (ty2 : Type) -> (rel2 : ty2 -> ty2 -> Type) -> (pf2 : IsEqRel ty2 rel2) ->
                       (f : (ty1 -> ty2)) -> (pf_f : Passes_Through ty1 rel1 ty2 rel2 f) ->
                       (g : (ty1 -> ty2)) -> (pf_g : Passes_Through ty1 rel1 ty2 rel2 g) ->
                       (h : (ty1 -> ty2)) -> (pf_h : Passes_Through ty1 rel1 ty2 rel2 h) ->
                       (Function_rel ty1 rel1 pf1 ty2 rel2 pf2 f g pf_f pf_g) ->
                       (Function_rel ty1 rel1 pf1 ty2 rel2 pf2 g h pf_g pf_h) ->
                       (Function_rel ty1 rel1 pf1 ty2 rel2 pf2 f h pf_f pf_h)
                       
IsTrans_Function_rel ty1 rel1 pf1 ty2 rel2 pf2 f pf_f g pf_g h pf_h pf_fg pf_gh a b pf_ab = let

    pf3 : (rel2 (f a) (g b))
        = pf_fg a b pf_ab

    pf_refl_1 : ((a1 : ty1) -> rel1 a1 a1)
        = (fst pf1)

    pf_refl_2 : ((a1 : ty2) -> rel2 a1 a1)
        = (fst pf2)

    -- pf4 : (rel2 (g b) (g b))
        -- = pf_refl_2 (g b)

    pf5 : (rel2 (g b) (h b))
        = pf_gh b b (pf_refl_1 b)

    pf_trans_2 : ((a1 : ty2) -> (b1 : ty2) -> (c : ty2) ->
                 (rel2 a1 b1) -> (rel2 b1 c) -> (rel2 a1 c))
        = (snd (snd pf2))

    pf6 : (rel2 (f a) (h b))
        = pf_trans_2 (f a) (g b) (h b) pf3 pf5

    in
    pf6



















{-
data Quotient_Dependent_Function : (ty : Type) -> (rel : ty -> ty -> Type) ->
                                  (P : (Quotient_Family ty rel)) -> Type where
    quotient_Dependent_Function : (a, b : ty) -> (rel a b) ->
                    -}
