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
IsCommRing ring (+) (*) = (IsRing ring (+) (*) , Commutative ring (*))


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

||| Rings that have zero divisors                                     
total
Ring_with_zero_divisor : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> (IsRing ring (+) (*)) -> Type
Ring_with_zero_divisor ring (+) (*) pfRing = (a : ring ** (b : ring ** Either (a*b = e) (b*a = e))) where
                                                                                                         e = fst (RingAdditive_id ring (+) (*) pfRing)
||| Integral Domain
total
IsIntegralDomain : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsIntegralDomain ring (+) (*) = (pfRing : IsCommRing ring (+) (*) ** (((a : ring) -> (b : ring) -> (a*b = fst (RingAdditive_id ring (+) (*) (fst pfRing))) -> (Either (a = fst (RingAdditive_id ring (+) (*) (fst pfRing))) (b = fst (RingAdditive_id ring (+) (*) (fst pfRing)))))))

||| Euclidian Norm
total
IsEuclidianNorm : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> (IsIntegralDomain ring (+) (*)) -> (norm : (ring -> Nat)) -> Type
IsEuclidianNorm ring (+) (*) pfIntDomain norm = ( ( (a : ring) -> (b : ring) -> (a = e -> Void) -> (b = e -> Void) -> (LTE (norm a) (norm (a*b))) ) , ( (a : ring) -> (b : ring) -> ((b = e -> Void)) -> (q : ring ** (r : ring ** ( (a = b*q + r) , (LTE (norm r) (norm b) )) )) ) ) where
                                                                                                                                                                                                                                                                                        e = fst (RingAdditive_id ring (+) (*) (fst (fst pfIntDomain)))
||| Euclidian Domain
total
IsEuclidianDomain : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsEuclidianDomain ring (+) (*) = (pfIntDomain : IsIntegralDomain ring (+) (*) ** (EuclNorm : (ring -> Nat) ** (IsEuclidianNorm ring (+) (*) pfIntDomain EuclNorm) ) )
 
                                      
                                      
                                      
