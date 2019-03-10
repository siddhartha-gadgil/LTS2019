module Group_property2

import congruence
import Monoid
import Group
import Group_property 

%access public export
                         
||| Property 8 - If f : g -> h is group homomorphism then f(inv(a)) = inv(f(a))
total
Group_property_8 : (dom : Type) -> ((*) : dom -> dom -> dom) -> (pfdom : IsGroup dom (*)) ->
                    (cod : Type) -> ((+) : cod -> cod -> cod) -> (pfcod : IsGroup cod (+)) ->
                    (f : dom -> cod) -> (pfhom : (Hom dom (MkGroup dom (*) pfdom) cod (MkGroup cod (+) pfcod) f)) -> 
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
                                                         pf7 = trans (trans pf4 (sym pf6)) pf5 -- proof that (f a) + (f a_inv) = e_cod1
                                                         pf8 = Group_property_7 cod (+) pfcod (f a) (f a_inv) pf7 -- proof that inverse of (f a) 
                                                                                                                  -- is (f a_inv)
                                                         pf9 = snd (Inv_with_pf cod (+) pfcod (f a)) -- proof that c is a inverse of (f a) with 
                                                                                                     -- e_cod2 as identity
                                                         pf9.1 = fst pf9 -- proof that (f a) + c = e_cod2
                                                         pf9.2 = snd pf9 -- proof that c + (f a) = e_cod2
                                                         pf10.1 = trans pf9.1 (sym pf_eq_cod_id12) -- proof that (f a) + c = e_cod1
                                                         pf10.2 = trans pf9.2 (sym pf_eq_cod_id12) -- -- proof that c + (f a) = e_cod1
                                                         pf10 = (pf10.1, pf10.2)
                                                          
                                                         in 
                                                         (Group_property_2 cod (+) pfcod (f a) b c pf8 pf10)
                                                         
||| Property 9 - If a*b = c then b = Inv(a) * c
total
Group_property_9 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) -> 
                   (a, b, c : grp) -> (a*b = c) -> (b = (Inv grp (*) pfgrp a)*c)
                                                         
Group_property_9 grp (*) pfgrp a b c pfEq = ?rhs                                      
                                                         
                                                         
                                                         
                                                         
                                                         
                                                         
                                                         
                                                         
                                                         
