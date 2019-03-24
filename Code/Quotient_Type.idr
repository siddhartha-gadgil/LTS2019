module Quotient_Type

%access public export
%default total

IsRefl : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsRefl typ rel = (a : typ) -> (rel a a)

IsSym : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsSym typ rel = (a, b : typ) -> (rel a b) -> (rel b a)

IsTrans : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsTrans typ rel = (a, b, c : typ) -> (rel a b) -> (rel b c)

IsEqRel : (typ : Type) -> (rel : typ -> typ -> Type) -> Type
IsEqRel typ rel = ( (IsRefl typ rel) , ( (IsSym typ rel), (IsTrans typ rel) ) )

data Quotient_Type : (typ : Type) -> (rel : typ -> typ -> Type) -> Type where
    quotient_Type : (IsEqRel typ rel) -> (Quotient_Type typ rel)
                    
Passes_Through : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) -> 
                 (ty2 : Type) -> (rel_2 : ty2 -> ty2 -> Type) -> 
                 (f : ty1 -> ty2) -> Type
                 
Passes_Through ty1 rel_1 ty2 rel_2 f = 
    (a, b : ty1) -> (rel_1 a b) -> (rel_2 (f a) (f b))
    
data Quotient_Function : (ty1 : Type) -> (rel_1 : ty1 -> ty1 -> Type) ->
                         (ty2 : Type) -> (rel_2 : ty2 -> ty2 -> Type) -> Type where
    quotient_Function : (f : ty1 -> ty2) -> (Passes_Through ty1 rel_1 ty2 rel_2 f) 
        -> (Quotient_Function ty1 rel_1 ty2 rel_2)   
                             
    
                     
                    
                    
