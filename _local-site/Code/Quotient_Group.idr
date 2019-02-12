module Quotient_Group

import Monoid
import Group

%access public export

||| Given a map f : g -> h, the image of f along with the proofs
total
ImageOf : (x : Type) -> (y : Type) -> (f : x -> y) -> Type
ImageOf x y f = (b : y ** (a : x ** ( (f a) = b)))

||| Generates the coset over h of a given element in g
total
Coset: (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) -> 
       (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) -> 
       (Subgroup h (+) pf1 g (*) pf2) -> (a : g) -> Type
Coset h (+) pf1 g (*) pf2 (f ** pfSub) a = (y : g ** (y1 : ImageOf h g f ** ((fst y1)*a = y)))
--Imgfn h g (\r => a*(fst(sbgrp) r))

||| The property that a particular element is in the coset
total
Is_in_Coset : (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) -> 
              (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) -> 
              (Subgroup h (+) pf1 g (*) pf2) -> (a : g) -> (b : g) -> Type
              
Is_in_Coset h (+) pf1 g (*) pf2 (f ** pfSub) a b = (y1 : ImageOf h g f ** ((fst y1)*a = b))

||| If b is in the coset of a, then a is in the coset of b
total
Coset_property_1 : (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) -> 
                   (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) -> 
                   (Subgroup h (+) pf1 g (*) pf2) -> (a : g) -> (b : g) ->
                   (Is_in_Coset  h (+) pf1 g (*) pf2 (f ** pfSub) a b) ->
                   (Is_in_Coset  h (+) pf1 g (*) pf2 (f ** pfSub) b a)

||| Property 2 - A proof that C(a) * C(b) and C(a*b) are equal as sets
total
Coset_property_2 : (h : Type) -> ((+) : h -> h -> h) -> (pf1 : IsGroup h (+)) -> 
                   (g : Type) -> ((*) : g -> g -> g) -> (pf2 : IsGroup g (*)) -> 
                   (Subgroup h (+) pf1 g (*) pf2) -> Type
