module Group_property

import Monoid
import Group

%access public export

||| Property 1 - Identity is unique for groups
total
Group_property_1 : (grp : Type) -> ((*) : grp -> grp -> grp) ->
                   (IsGroup grp (*)) -> (e1 : grp) -> (e2 :grp) ->
                   (IsIdentity grp (*) e1) -> (IsIdentity grp (*) e2) ->
                   (e1 = e2)
                   
Group_property_1 grp (*) pf_grp e1 e2 pf1 pf2 = trans (sym(snd (pf2 e1))) (fst (pf1 e2)) 

||| Property 2 - Inverse of an element is unique
total
Group_property_2 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) ->
                   (a : grp) -> (b : grp) -> (c : grp) ->
                   (IsInverse grp (*) (fst(snd pfgrp)) a b) ->
                   (IsInverse grp (*) (fst(snd pfgrp)) a c) -> (b = c)
                   
Group_property_2 grp (*) (pfAss, (pfid, pfinv)) a b c pfb pfc = rewrite (sym (fst ((snd pfid) b))) in 
                                                               (rewrite (sym (fst pfc)) in 
                                                               (rewrite (sym (pfAss b a c)) in 
                                                               (rewrite (snd pfb) in 
                                                               (rewrite (snd ((snd pfid) c)) in Refl))))                   

||| Property 3 - b = c implies a*b = a*c 
total
Group_property_3 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) ->
                   (a : grp) -> (b : grp) -> (c : grp) -> (b = c) -> (a*b = a*c)
Group_property_3 grp (*) pfgrp a b c pfEq = cong pfEq

||| Property 4 - a*b = a*c implies b = c
total
Group_property_4 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) ->
                   (a : grp) -> (b : grp) -> (c : grp) -> (a*b = a*c) -> (b = c)
Group_property_4 grp (*) pfgrp a b c pfEq = let pfid = (fst (snd (snd pfgrp))) 
                                                a_inv = fst(Inv_with_pf grp (*) pfgrp a)
                                                pf_inv = snd(Inv_with_pf grp (*) pfgrp a)
                                                pfAss = fst pfgrp
                                                in 
                                                (rewrite (sym (snd ((snd pfid) b))) in 
                                                (rewrite (sym (snd ((snd pfid) c))) in 
                                                (rewrite (sym (snd pf_inv)) in 
                                                (rewrite (pfAss a_inv a b) in 
                                                (rewrite (pfAss a_inv a c) in 
                                                (Group_property_3 grp (*) pfgrp a_inv (a*b) (a*c) pfEq))))))              
                                                
                                                
                                                
                                                
                                                
                                                
                                                
