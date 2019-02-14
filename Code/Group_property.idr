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
                   
Group_property_2 grp (*) pfgrp a b c pfb pfc = let
                                               pfAss = fst pfgrp
                                               pfid = (fst (snd pfgrp))	
                                               in
                                               rewrite (sym (fst ((snd pfid) b))) in 
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

||| Auxilliary proof 1 - Two idenitities mentioned in the definition of the group 
||| (one in (fst (snd pfgrp)) another in (fst (snd (snd pfgrp))) are equal.
total
Group_aux_pf_1 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : (IsGroup grp (*))) ->
                 ( (fst (Group_id grp (*) pfgrp)) = (fst (fst (snd (snd pfgrp)))) ) 
 
Group_aux_pf_1 grp (*) pfgrp = let 
                               pfid1 = (Group_id grp (*) pfgrp)
                               e1 = (fst pfid1)
                               pf1 = (snd pfid1)
                               pfid2 = (fst (snd (snd pfgrp)))
                               e2 = (fst pfid2)
                               pf2 = (snd pfid2)
                               in
                               (Group_property_1 grp (*) pfgrp e1 e2 pf1 pf2)
                                 
||| Property 7 - One sided inverse is two sided inverse
total
Group_property_7 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : (IsGroup grp (*))) -> (a : grp)
                   -> (b : grp) -> ( (a*b) = (fst (Group_id grp (*) pfgrp)) )
                   -> (IsInverse grp (*) (Group_id grp (*) pfgrp) a b)
                   
Group_property_7 grp (*) pfgrp a b pfEq = let
                                          pfid1 = Group_id grp (*) pfgrp -- Identity in IdentityExists
                                          pfid2 = fst (snd (snd pfgrp)) -- Identity in InverseExists
                                          e1 = (fst pfid1)
                                          e2 = (fst pfid2)
                                          a_inv = Inv grp (*) pfgrp a
                                          a_inv_pf = snd (Inv_with_pf grp (*) pfgrp a)
                                          a_inv_pf1 = (fst a_inv_pf) -- Proof that a*a_inv = e2
                                          a_inv_pf2 = (snd a_inv_pf) -- Proof that a_inv*a = e2
                                          pfId_eq = Group_aux_pf_1 grp (*) pfgrp -- proof that e1 = e2
                                          pf1 = trans a_inv_pf1 (sym pfId_eq) -- proof that a*a_inv = e1
                                          pf2 = trans pf1 (sym pfEq) -- proof that a*a_inv = a*b
                                          pf3 = Group_property_4 grp (*) pfgrp a a_inv b pf2 -- proof that a_inv b 
                                          pf4 = trans a_inv_pf2 (sym pfId_eq) -- proof that a_inv*a = e1
                                          pf5 = Group_property_5 grp (*) pfgrp a a_inv b pf3 -- proof that a_inv*a = b*a
                                          pf6 = trans (sym pf5) pf4
                                          in
                                          (pfEq, pf6)  

                                                         
                                                
                                                
                                                
                                                
                                                
                                                
                                                
                                                
                                                
