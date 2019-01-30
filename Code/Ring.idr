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

total
IsCommRing : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsCommRing ring (+) (*) = (IsRing ring (+) (*) , Commutative ring (+))


||| Gives the additive identity of the ring
RingAdditive_id : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> 
                  (IsRing ring (+) (*)) -> (IdentityExists ring (+))
RingAdditive_id ring (+) (*) ((pfGrp,pfAb), pfElse) = Group_id ring (+) pfGrp


||| Non Zero elements in a ring
Ring_NonZero_Elements : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> 
                        (IsRing ring (+) (*)) -> Type
Ring_NonZero_Elements ring (+) (*) pfRing = (a : ring ** ((a = e) -> Void)) where 
                                             e = fst (RingAdditive_id ring (+) (*) pfRing)                  
||| Type of rings with identity
total
IsRing_with_identity : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsRing_with_identity ring (+) (*) = (pfRing : IsRing ring (+) (*) **
                                    ( iden : (Ring_NonZero_Elements ring (+) (*) pfRing) ** 
                                      (a : ring) -> ((a*(fst iden) = a) , ((fst iden)*a = a))))
                                      
||| Useful rings - i.e commutative rings with identity
total
IsUsefulRing :  (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsUsefulRing ring (+) (*) = (IsRing_with_identity ring (+) (*), IsCommRing ring (+) (*))                                     
                                      
                                      
                                      
                                      
