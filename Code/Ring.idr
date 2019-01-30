module Rings

import Monoid
import Group

%access public export

||| Distributive Law
total
IsDistributive : (typ : Type) -> ((+) : typ -> typ -> typ) 
                  -> ((*) : typ -> typ -> typ) -> Type
IsDistributive typ (+) (*) = (a,b,c : typ) -> ( (a*(b + c) = (a*b) + (a*c)), ((b + c)*a = (b*a) + (b*c)) )

total
IsRing : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsRing ring (+) (*) = (IsAbelianGrp ring (+), (IsMonoid ring (*), IsDistributive ring (+) (*))) 
