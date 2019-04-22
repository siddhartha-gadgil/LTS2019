module Rings

import Monoid
import Group

%access public export

||| Distributive Law
total
IsDistributive : (typ : Type) -> ((+) : typ -> typ -> typ)
                  -> ((*) : typ -> typ -> typ) -> Type
IsDistributive typ (+) (*) = (a,b,c : typ) -> ( (a*(b + c) = (a*b) + (a*c)), ((b + c)*a = (b*a) + (c*a)) )

||| The type of proofs that a given type is a ring
total
IsRing : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsRing ring (+) (*) = (IsAbelianGrp ring (+), (Associative ring (*), IsDistributive ring (+) (*)))

||| The type of proofs that a given type is a commutative ring
total
IsCommRing : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsCommRing ring (+) (*) = (IsRing ring (+) (*) , Commutative ring (*))

||| Data type for rings
data Ring: (ring: Type) -> Type where
  MkRing: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> IsRing ring (+) (*) -> Ring ring

||| Data type for commutative rings
data CRing: (ring: Type) -> Type where
  MkCRing: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> IsCommRing ring (+) (*) -> CRing ring

|||A function that outputs the addition operation of a ring structure
Ring_Add: (ring: Type) -> Ring ring -> ring -> ring -> ring
Ring_Add ring (MkRing ring (+) (*) x) y z = y+z

|||A function that outputs the multiplication operation of a ring structure
Ring_Mult: (ring: Type) -> Ring ring -> ring -> ring -> ring
Ring_Mult ring (MkRing ring (+) (*) x) y z = y*z

||| Gives the additive identity of the ring
total
RingAdditive_id : (ring : Type) -> (pfr: Ring ring) -> (IdentityExists ring (Ring_Add ring pfr))
RingAdditive_id ring (MkRing ring (+) (*) ((pfGrp,pfAb), pfElse)) = Group_id ring (+) pfGrp

||| Non Zero elements in a ring
total
Ring_NonZero_Elements : (ring : Type) -> Ring ring -> Type
Ring_NonZero_Elements ring pfr = (a : ring ** ((a = e) -> Void)) where
                                             e = fst (RingAdditive_id ring pfr)

||| Type of rings with identity
total
IsRing_with_identity : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsRing_with_identity ring (+) (*) = (IsAbelianGrp ring (+), (IsMonoid ring (*), IsDistributive ring (+) (*)))

||| Useful rings - i.e commutative rings with identity
total
IsUsefulRing :  (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsUsefulRing ring (+) (*) = (IsRing_with_identity ring (+) (*), IsCommRing ring (+) (*))

|||Data type for rings with identity
data Ring_with_identity: (ring: Type) -> Type where
  MkRing_with_identity: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> IsRing_with_identity ring (+) (*) -> Ring_with_identity ring

|||Dat atypes for Useful rings
data URing: (ring: Type) -> Type where
  MkURing: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> IsUsefulRing ring (+) (*) -> URing ring

||| A function that demonstrates that every Useful ring is commutative
total
URingisCRing: (ring: Type) -> URing ring -> CRing ring
URingisCRing ring (MkURing ring ((+)) ((*)) (a, b)) = MkCRing ring (+) (*) b

|||A function that demonstrates that every commutative ring is a ring
total
CRingisRing: (ring: Type) -> CRing ring -> Ring ring
CRingisRing ring (MkCRing ring ((+)) ((*)) (a, b)) = MkRing ring (+) (*) a

||| A function that demonstrates that every Useful ring is commutative
total
URingisRing_with_identity: (ring: Type) -> URing ring -> Ring_with_identity ring
URingisRing_with_identity ring (MkURing ring ((+)) ((*)) (a, b)) = MkRing_with_identity ring (+) (*) a

||| A function that demonstrates that every ring with identity is a ring
total
Ring_with_identity_isRing: (ring: Type) -> Ring_with_identity ring -> Ring ring
Ring_with_identity_isRing ring (MkRing_with_identity ring ((+)) ((*)) (a, b)) = MkRing ring (+) (*) (a, ((Basics.fst (Basics.fst b)), (Basics.snd b)))

|||A function that outputs the addition operation of a ring structure (with identity) - seemed more convenient than proving that the addition operation arising from the Ring_Add function is the right one
IRing_Add: (ring: Type) -> Ring_with_identity ring -> ring -> ring -> ring
IRing_Add ring (MkRing_with_identity ring (+) (*) x) y z = y +z

|||A function that outputs the multiplication operation of a ring structure (with identity)
IRing_Mult: (ring: Type) -> Ring_with_identity ring -> ring -> ring -> ring
IRing_Mult ring (MkRing_with_identity ring (+) (*) x) y z = y*z

Ring_Mult_identity: (ring: Type) -> (pfr: Ring_with_identity ring) -> DPair ring (\e => IsIdentity ring (IRing_Mult ring pfr) e)
Ring_Mult_identity ring (MkRing_with_identity ring (+) (*) x) = Basics.snd (Basics.fst (Basics.snd x))

||| Rings that have zero divisors
total
Ring_with_zero_divisor : (ring : Type) -> Ring ring -> Type
Ring_with_zero_divisor ring (MkRing ring (+) (*) pfRing) = (a : ring ** (b : ring ** Either (a*b = e) (b*a = e))) where
                                  e = DPair.fst (RingAdditive_id ring (MkRing ring (+) (*) pfRing))

||| The type of proofs that a given type is an Integral Domain
total
IsIntegralDomain : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsIntegralDomain ring (+) (*) = (pfRing : IsUsefulRing ring (+) (*) ** (((a : ring) -> (b : ring) -> (a*b = fst (RingAdditive_id ring (MkRing ring (+) (*) (fst (snd pfRing))) )) -> (Either (a = fst (RingAdditive_id ring (MkRing ring (+) (*) (fst (snd pfRing))) )) (b = fst (RingAdditive_id  ring (MkRing ring (+) (*) (fst (snd pfRing))) )) ) )) )

||| Data type for integral domains
data IntegralDomain: (ring: Type) -> Type where
  MkIntegralDomain: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> IsIntegralDomain ring (+) (*) -> IntegralDomain ring

|||The type of ring homomorphisms (between rings with identity)
IRHom: (r1: Type) -> Ring_with_identity r1 -> (r2: Type) -> Ring_with_identity r2 -> (f: r1 -> r2) -> Type
IRHom r1 (MkRing_with_identity r1 ((+)) ((*)) pf1) r2 (MkRing_with_identity r2 ((p)) ((m)) pf2) f = (x: r1) -> (y: r1) -> ((f(x+y)) =  (p (f x) (f y)), (f(x*y)) = (m (f x) (f y)), (f e1) = e2) where
  e1 = DPair.fst (Ring_Mult_identity r1 (MkRing_with_identity r1 ((+)) ((*)) pf1))
  e2 = DPair.fst (Ring_Mult_identity r2 (MkRing_with_identity r2 (p) (m) pf2))

|||The type of more flexible ring homomorphisms
RHom:(r1: Type) -> Ring r1 -> (r2: Type) -> Ring r2 -> (f: r1 -> r2) -> Type
RHom r1 (MkRing r1 ((+)) ((*)) pf1) r2 (MkRing r2 ((p)) ((m)) pf2) f = (x: r1) -> (y: r1) -> ((f(x+y)) =  (p (f x) (f y)), (f(x*y)) = (m (f x) (f y)))

|||The type of ideals
IsIdeal: (i: Type) -> Ring i -> (r: Type) -> Ring r -> Type
IsIdeal i pfi r pfr = (DPair (i -> r) (\f => (Inj i r f, RHom i pfi r pfr f, (p: r) -> (t: i) -> (q: i ** ((f q) = (Ring_Mult r pfr p (f t)))) )))

|||The type of principal ideals
IsPrincipalIdeal: (i: Type) -> Ring i -> (r: Type) -> Ring r -> IsIdeal i pfi r pfr -> Type
IsPrincipalIdeal i pfi r pfr (f ** pf) = (p:i ** ((t: i) -> (x: r ** (f t) = (Ring_Mult r pfr x (f p)))) )

|||The type of PID's
IsPID: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsPID ring (+) (*) = (pfURing : IsUsefulRing ring (+) (*) ** ((i: Type) -> (pfi: Ring i) -> (pfIdeal: IsIdeal i pfi ring (CRingisRing ring (URingisCRing ring (MkURing ring (+) (*) pfURing))) ) -> IsPrincipalIdeal i pfi ring (CRingisRing ring (URingisCRing ring (MkURing ring (+) (*) pfURing))) pfIdeal) )

||| Data type for PIDs
data PID: (ring: Type) -> Type where
  MkPID: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> IsPID ring (+) (*) -> PID ring

||| Euclidean Norm
total
IsEuclideanNorm : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> (IsIntegralDomain ring (+) (*)) -> (norm : (ring -> Nat)) -> Type
IsEuclideanNorm ring (+) (*) pfIntDomain norm = ( ( (a : ring) -> (b : ring) -> (a = e -> Void) -> (b = e -> Void) -> (LTE (norm a) (norm (a*b))) ) , ( (a : ring) -> (b : ring) -> ((b = e -> Void)) -> (q : ring ** (r : ring ** ( (a = b*q + r) , (LTE (norm r) (norm b) )) )) ) ) where
                                                                                                                                                                                                                                                                              e = fst (RingAdditive_id ring (MkRing ring (+) (*) (fst (snd (fst pfIntDomain))) ) )
||| Euclidean Domain
total
IsEuclideanDomain : (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> Type
IsEuclideanDomain ring (+) (*) = (pfIntDomain : IsIntegralDomain ring (+) (*) ** (EuclNorm : (ring -> Nat) ** (IsEuclideanNorm ring (+) (*) pfIntDomain EuclNorm) ) )

||| Data type for PIDs
data EuclideanDomain: (ring: Type) -> Type where
  MkEuclideanDomain: (ring : Type) -> ((+) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring) -> IsEuclideanDomain ring (+) (*) -> EuclideanDomain ring
