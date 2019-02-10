module Group_property

import Monoid
import Group
import congruence

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
                                                
||| Property 5 - b = c implies b*a = c*a 
total
Group_property_5 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) ->
                   (a : grp) -> (b : grp) -> (c : grp) -> (b = c) -> ( (b*a) = (c*a) )
Group_property_5 grp (*) pfgrp a b c pfEq = (congruence grp grp b c (\x : grp => x*a) pfEq) 

||| Property 6 - b*a = c*a implies b = c
total
Group_property_6 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) ->
                   (a : grp) -> (b : grp) -> (c : grp) -> (b*a = c*a) -> (b = c)
Group_property_6 grp (*) pfgrp a b c pfEq = let pfid = (fst (snd (snd pfgrp))) 
                                                a_inv = fst(Inv_with_pf grp (*) pfgrp a)
                                                pf_inv = snd(Inv_with_pf grp (*) pfgrp a)
                                                pfAss = fst pfgrp
                                                in
                                                (rewrite (sym (fst ((snd pfid) b))) in  
                                                (rewrite (sym (fst ((snd pfid) c))) in 
                                                (rewrite (sym (fst pf_inv)) in 
                                                (rewrite (sym (pfAss b a a_inv)) in 
                                                (rewrite (sym (pfAss c a a_inv)) in 
                                                (Group_property_5 grp (*) pfgrp a_inv (b*a) (c*a) pfEq))))))
                         
||| Property 8 - If f : g -> h is group homomorphism then f(inv(a)) = inv(f(a))
total
Group_property_8 : (dom : Type) -> ((*) : dom -> dom -> dom) -> (pfdom : IsGroup dom (*)) ->
                    (cod : Type) -> ((+) : cod -> cod -> cod) -> (pfcod : IsGroup cod (+)) ->
                    (f : dom -> cod) -> (pfhom : (Hom dom (*) pfdom cod (+) pfcod f)) -> 
                    (a : dom) -> ( (f (Inv dom (*) pfdom a)) = (Inv cod (+) pfcod (f a)) )
                   
Group_property_8 dom (*) pfdom cod (+) pfcod f pfhom a = let
                                                         pfid1_dom = (fst (snd pfdom))
                                                         e_dom1 = (fst pfid1_dom) -- identity in the IdentityExists
                                                         e_dom1_pf = (snd pfid1_dom) -- proof that e_dom1 is the identity
                                                         
                                                         pfid2_dom = (fst (snd (snd pfdom)))
                                                         e_dom2 = (fst pfid2_dom) -- identity in the InverseExists
                                                         e_dom2_pf = (snd pfid2_dom) -- prood that it is the identity
                                                         
                                                         pf_eq_dom_id12 = (Group_property_1 dom (*) pfdom e_dom1 e_dom2
                                                                            e_dom1_pf e_dom2_pf) -- proof that e_dom1 and e_dom2 are equal
                                                                            
                                                         pfid1_cod = (fst (snd pfcod))
                                                         e_cod1 = (fst pfid1_cod) -- identity in the IdentityExists
                                                         e_cod1_pf = (snd pfid1_cod) -- proof that e_cod1 is the identity
                                                         
                                                         pfid2_cod = (fst (snd (snd pfcod)))
                                                         e_cod2 = (fst pfid2_cod) -- identity in the InverseExists
                                                         e_cod2_pf = (snd pfid2_cod) -- prood that it is the identity
                                                         
                                                         pf_eq_cod_id12 = (Group_property_1 cod (+) pfcod e_cod1 e_cod2
                                                                            e_cod1_pf e_cod2_pf) -- proof that e_cod1 and e_cod2 are equal
                                                          
                                                         a_inv_with_pf = snd (snd (snd pfdom)) a -- (Inv_with_pf dom (*) pfdom a)
                                                         a_inv = fst a_inv_with_pf	
                                                         b = (f a_inv)
                                                         c = (Inv cod (+) pfcod (f a))
                                                         
                                                         pf_id_to_id = (fst pfhom)
                                                         pf_res = (snd pfhom)
                                                         
                                                         --aux_pf1 : ( ( Group_id dom (*) pfdom ) = (fst (snd pfdom)) )
                                                         --aux_pf1 = Refl -- proof that fst (Group_id dom (*) pfdom) = fst (fst (snd pfdom))
                                                         
                                                         pf1 = (pf_res a a_inv) -- proof that f(a * a_inv) = f a + f a_inv
                                                         pf2 = (fst (snd a_inv_with_pf)) -- proof that a * a_inv = e_dom2
                                                         pf3 = congruence dom cod (a * a_inv) e_dom2 f pf2 -- proof that a * a_inv = e_dom2
                                                         pf4 = trans (sym pf1) pf3 -- proof that f(a * a_inv) = f e_dom2
                                                         pf5 = (Group_property_1 cod (+) pfcod 
                                                               (f e_dom1) e_cod1 pf_id_to_id e_cod1_pf) -- proof that f e_dom1 = e_cod1
                                                         pf6 = congruence dom cod e_dom1 e_dom2 f pf_eq_dom_id12-- proof that f e_dom1 = f e_dom2
                                                         pf7 = trans (trans pf4 (sym pf6)) pf5 
                                                          
                                                         in 
                                                         (Group_property_2 cod (+) pfcod (f a) b c (pf7,?rhs1) ?rhs2)
                                                         

                                                
                                                
                                                
                                                
                                                
                                                
                                                
                                                
                                                
