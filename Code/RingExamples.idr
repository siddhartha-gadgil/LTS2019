module RingExamples

import Ring
import RingProperties
import Group
import Group_property
import ZZ
import ZZUtils
import Monoid

%access public export

ZZAbGrp: IsAbelianGrp ZZ (+)
ZZAbGrp = ((Assoc, (((Pos Z)**PrfZ), (((Pos Z)**PrfZ)**PfInv))), CommutativeZ) where
  Assoc: (l,c,r:ZZ) -> (l+c)+r = l +(c+r)
  Assoc l c r = sym (plusAssociativeZ l c r)
  PrfZ: (a: ZZ) -> (a+(Pos Z) = a, (Pos Z) + a = a)
  PrfZ a = (plusZeroRightNeutralZ a, plusZeroLeftNeutralZ a)
  PfInv: (a: ZZ) -> DPair ZZ (\a_inv => ((a + a_inv = Pos Z), (a_inv + a = Pos Z)))
  PfInv a = MkDPair (negate a) (plusNegateInverseLZ a, plusNegateInverseRZ a)
  CommutativeZ: (a: ZZ) -> (b: ZZ) -> (a + b = b+a)
  CommutativeZ = plusCommutativeZ

ZZAssoc: Associative ZZ (*)
ZZAssoc l c r = sym (multAssociativeZ l c r)

ZZDist: IsDistributive ZZ (+) (*)
ZZDist l c r = (multDistributesOverPlusRightZ l c r, multDistributesOverPlusLeftZ c r l)

ZZMultCommutes: Commutative ZZ (*)
ZZMultCommutes = multCommutativeZ

ZZIsCRing: IsCommRing ZZ (+) (*)
ZZIsCRing = ((ZZAbGrp, (ZZAssoc, ZZDist)), ZZMultCommutes)

ZZCRing: CRing ZZ
ZZCRing = MkCRing ZZ (+) (*) ZZIsCRing
