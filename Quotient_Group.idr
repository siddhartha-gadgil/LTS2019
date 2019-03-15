module Quotient_Group

import Monoid
import Group
import Group_property
import Group_property2

%access public export

||| Given a map f : g -> h, the image of f along with the proofs
total
ImageOf : (x : Type) -> (y : Type) -> (f : x -> y) -> Type
ImageOf x y f = (b : y ** (a : x ** ( (f a) = b)))

||| Generates the (right) coset over h of a given element in g
total
Coset: (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) ->
       (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) ->
       (Subgroup h (MkGroup h (+) pf1) g (MkGroup g (*) pf2)) -> (a : g) -> Type

Coset h (+) pf1 g (*) pf2 (f ** pfSub) a = (y : g ** (y1 : ImageOf h g f ** ((fst y1)*a = y)))
--Imgfn h g (\r => a*(fst(sbgrp) r))

||| The property that a particular element is in the coset
total
Is_in_Coset : (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) ->
              (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) ->
              (Subgroup h (MkGroup h (+) pf1) g (MkGroup g (*) pf2)) -> (a : g) -> (b : g) -> Type

Is_in_Coset h (+) pf1 g (*) pf2 (f ** pfSub) a b = (y1 : ImageOf h g f ** ((fst y1)*a = b))

||| If b is in the coset of a, then a is in the coset of b
total
Coset_property_1 : (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) ->
                   (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) ->
                   (pfSub: Subgroup h (MkGroup h (+) pf1) g (MkGroup g (*) pf2)) -> (a : g) -> (b : g) ->
                   (Is_in_Coset  h (+) pf1 g (*) pf2 pfSub a b) ->
                   (Is_in_Coset  h (+) pf1 g (*) pf2 pfSub b a)

-- Coset_property_1 h (+) pfh g (*) pfg pfSub a b pf_a_in_Cb = let
--                                                             y = fst (fst pf_a_in_Cb)
--                                                             x = fst (snd (fst pf_a_in_Cb))
--                                                             pf_fx_is_y = (snd (snd (fst pf_a_in_Cb))) -- proof that (f x) = y
--                                                             pfy = snd pf_a_in_Cb -- proof that y*a = b
--
--                                                             f = (fst pfSub) -- the inclusion map from h to g
--                                                             pfhom = (fst (snd pfSub)) -- proof that f is a homomorphism
--
--                                                             x1 = Inv h (+) pfh x
--                                                             y1.1 = (f x1)
--                                                             y1.2 = Inv g (*) pfg y
--                                                             pf_y12_eq = (Group_property_8 h (+) pfh g (*) pfg f pfhom x1) -- proof that
--                                                                                                                         -- y1.1 = y1.2
--
--
--                                                             in
--                                                             ?rhs
                   
{-
||| Property 2 - A proof that C(a) * C(b) and C(a*b) are equal as sets
total
Coset_property_2 : (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) ->
                   (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) ->
                   (Subgroup h (+) pf1 g (*) pf2) -> Type
-}
