module Group.FiniteGenerate


import Group

%access public export



--proof that one element divides another in a group


-- element is generator if it is in the group and there is no element in the group that divides it

-- Create the collection of generators with their order

-- generates g^n given a group element g and n : Nat
Pow : (grp : Type) -> ((*) : grp -> grp -> grp) -> IsGroup grp (*) -> (g : grp) -> (n : Nat) -> grp
Pow grp (*) pfgrp g Z = fst (Group_id grp (*) pfgrp)
Pow grp (*) pfgrp g (S k) = g*(Pow grp (*) pfgrp g k)



-- check that group is finitely generated
HasFiniteOrder : (grp : Type) -> ((*) : grp -> grp -> grp) -> IsGroup grp (*) -> (g : grp) -> Type
HasFiniteOrder grp (*) pfgrp g = (n : Nat ** (LT Z n, Pow grp (*) pfgrp g n = fst (Group_id grp (*) pfgrp)))
