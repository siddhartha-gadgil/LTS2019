module Field

import Group
import Monoid
import Ring

%access public export


-- For field, proof that multiplicative inverse exists when only non zero elements are considered
total
InvExistsNonZero : (fld : Type) -> ((+) : fld -> fld -> fld) -> ((*) : fld -> fld -> fld) -> (IsGroup fld (+)) -> Type
InvExistsNonZero fld (+) (*) pfgrp = (a : fld) -> (pfid : (IdentityExists fld (*)) ** ((a = fst(fst(snd(pfgrp)))) -> Void) -> (a_inv : fld ** ((a*a_inv) = fst(pfid) , (a_inv*a) = fst(pfid))))


-- multiplication has associativity, identity, but inverse only for non-zero elements
total
IsModGrp : (fld : Type) -> ((+) : fld -> fld -> fld) -> ((*) : fld -> fld -> fld) -> (pfgrp : IsGroup fld (+)) -> Type
IsModGrp fld (+) (*) pfgrp = (Associative fld (*), (IdentityExists fld (*), InvExistsNonZero fld (+) (*) pfgrp))


-- modified abelian property added to the above proof
IsModAbelGrp : (fld : Type) -> ((+) : fld -> fld -> fld) -> ((*) : fld -> fld -> fld) -> (pfgrp : IsGroup fld (+)) -> Type
IsModAbelGrp fld (+) (*) pfgrp = (IsModGrp fld (+) (*) pfgrp, Commutative fld (*))


-- similar to Arka's file on monoids
total
IsField : (fld : Type) -> ((+) : fld -> fld -> fld) -> ((*) : fld -> fld -> fld) -> Type
IsField fld (+) (*) = (pfgrp: IsAbelianGrp fld (+) ** ((IsModAbelGrp fld (+) (*) (fst pfgrp)), IsDistributive fld (+) (*))) 
