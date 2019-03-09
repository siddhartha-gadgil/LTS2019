module Group_property3

import congruence
import Monoid
import Group
import Group_property 
import Group_property2

%access public export
%default total


||| Property 9 - If a*b = c then b = Inv(a) * c
total
Group_property_9 : (grp : Type) -> ((*) : grp -> grp -> grp) -> (pfgrp : IsGroup grp (*)) -> 
                   (a, b, c : grp) -> (a*b = c) -> (b = (Inv grp (*) pfgrp a)*c)
                                                         
Group_property_9 grp (*) pfgrp a b c pfEq = let
    a_inv = fst(Inv_with_pf grp (*) pfgrp a)
    pf_inv = snd(Inv_with_pf grp (*) pfgrp a)
    
    pf1 = Group_property_3 grp (*) pfgrp a_inv (a*b) c pfEq -- a_inv * (a * b) = a_inv * c
    pfAss = fst pfgrp -- proof of associativity
    pf2 = pfAss a_inv a b -- a_inv * (a * b) = (a_inv * a) * b
    
    pf3 = snd pf_inv -- a_inv * a = e2                                       
    
    pfid1 = (fst (snd pfgrp))
    e1 = (fst pfid1) -- identity in the IdentityExists
    e1_pf = (snd pfid1) -- proof that e_dom1 is the identity
    
    pfid2 = (fst (snd (snd pfgrp)))
    e2 = (fst pfid2) -- identity in the InverseExists
    e2_pf = (snd pfid2) -- prood that it is the identity
    
    pf_eq_e12 = (Group_property_1 grp (*) pfgrp e1 e2 e1_pf e2_pf) -- e1 = e2
    
    pf4 = trans pf3 (sym pf_eq_e12) -- a_inv * a = e1
    pf5 = Group_property_5 grp (*) pfgrp b (a_inv * a) e1 pf4 -- (a_inv * a) * b = e1 * b
    pf6 = e1_pf b 
    pf7 = fst pf6 -- b * e1 = b
    pf8 = snd pf6 -- e1 * b = b
    pf9 = trans pf5 pf8 -- a_inv * a * b = b
    pf10 = trans (sym pf2) pf9 -- a_inv * (a * b) = b 
    pf11 = trans (sym pf1) pf10 -- a_inv * c = b
    in
    (sym pf11)    
