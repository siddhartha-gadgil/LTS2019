module Group_kernel

import congruence
import Monoid
import Group

%access public export

%default total

IsKernel : (ker : Type) -> ((.) : ker -> ker -> ker) -> (pfker : (IsGroup ker (.))) ->
           (dom : Type) -> ((*) : dom -> dom -> dom) -> (pfdom : (IsGroup dom (*))) ->
           (Subgroup1 ker (.) pfker dom (*) pfdom) ->
           (cod : Type) -> ((+) : cod -> cod -> cod) -> (IsGroup cod (+)) -> 
           (f : dom -> cod) -> (Hom1 dom (*) pfdom cod (+) pfcod f) -> Type
                      
IsKernel ker (.) pfker dom (*) pfdom (f ** pfsub) cod (+) pfcod g pfhom = 
    (a : ker ** ( (g (f a)) = (fst (Group_id cod (+) pfcod)) ))  

{-   
||| Proof that kernel is a normal subgroup
    
Kernel_property_1 : (ker : Type) -> (.) -> (pfker : (Group ker)) -> 
                    (grp : Type) -> )*)(pfgrp : (Group grp)) -> 
                    (cod : Type) -> 
                    ()
-}




 
