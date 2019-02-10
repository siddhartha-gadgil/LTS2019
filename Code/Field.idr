module Ring

import Group
import Monoid
import Ring

%access public export

-- similar to Arka's file on monoids
total
isField : (fld : Type) -> ((+) : fld -> fld -> fld) -> ((*) : fld -> fld -> fld) -> Type
IsField fld (+) (*) = (IsAbelianGrp fld (+), (IsAbelianGrp fld (*), IsDistributive fld (+) (*)))
