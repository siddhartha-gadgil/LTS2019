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

Passes_Through : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) ->
                 (ty2 : Type) -> (rel_2 : ty2 -> ty2 -> Type) ->
                 (f : ty1 -> ty2) -> Type

Passes_Through ty1 rel_1 ty2 rel_2 f =
    (a, b : ty1) -> (rel_1 a b) -> (rel_2 (f a) (f b))

data Quotient_Function : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) ->
                         (ty2 : Type) -> (rel_2 : ty2 -> ty2 -> Type) -> Type where

    Cons_quotient_Function : (f : ty1 -> ty2) -> (Passes_Through ty1 rel_1 ty2 rel_2 f)
        -> (Quotient_Function ty1 rel_1 ty2 rel_2)

Transport_of : (ty : Type) -> (rel : ty -> ty -> Type) -> (P : ty -> Type) -> Type
Transport_of ty rel P = (a, b : ty) -> (rel a b) -> (P a) -> (P b)

data Quotient_Family : (ty : Type) -> (rel : ty -> ty -> Type) -> Type where
    Cons_quotient_Family : (P : ty -> Type) -> (Transport_of ty rel P) -> (Quotient_Family ty rel)

get_Family : (ty : Type) -> (rel : ty -> ty -> Type) -> (P : (Quotient_Family ty rel)) ->
             (ty -> Type)
get_Family ty rel (Cons_quotient_Family p tr) = p

get_Transport : (ty : Type) -> (rel : ty -> ty -> Type) -> (P : (Quotient_Family ty rel)) ->
                (Transport_of ty rel (get_Family ty rel P))
get_Transport ty rel (Cons_quotient_Family P tr) = tr


Passes_Through_Dependent : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) ->
                           (P : (Quotient_Family ty1 rel_1)) ->
                           (relP : (a : ty1) -> ((get_Family ty1 rel_1 P) a) -> ((get_Family ty1 rel_1 P) a) -> Type) ->
                           (f : (a : ty1) -> ((get_Family ty1 rel_1 P) a) ) -> Type

Passes_Through_Dependent ty1 rel_1 P relP f = (a, b : ty1) -> (pt : rel_1 a b) ->
    ( (relP b) ((get_Transport ty1 rel_1 P) a b pt (f a)) (f b))

EqRel_factors_through_Eq : (ty : Type) -> (rel : ty -> ty -> Type) -> (IsEqRel ty rel) ->
                           (a, b : ty) -> (a = b) -> (rel a b)

EqRel_factors_through_Eq ty rel pfEqRel a a Refl = (fst pfEqRel) a

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


{-
data Quotient_Dependent_Function : (ty : Type) -> (rel : ty -> ty -> Type) ->
                                  (P : (Quotient_Family ty rel)) -> Type where
    quotient_Dependent_Function : (a, b : ty) -> (rel a b) ->
                    -}
