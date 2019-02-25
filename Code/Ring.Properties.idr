module RingProperties

import Ring
import Monoid
import Group
import Group_property

%access public export

|||Auxiliary function that provzs that if a+a=a thzn a=0
aplusaZ: (r: Type) -> (pfr: Ring r) -> (a: r) -> ((Ring_Add r pfr a a) =a) -> (a = (DPair.fst(RingAdditive_id r pfr)))
aplusaZ r (MkRing r (+) (*) pfr) a prf = (Group_property_4 r (+) (Basics.fst (Basics.fst pfr)) a a z (trans prf (sym (Basics.fst (pfz a))) )) where
  z: r
  z = (DPair.fst(RingAdditive_id r (MkRing r (+) (*) pfr)))
  pfz: (a: r) -> (a+z=a, z+a=a)
  pfz = DPair.snd (RingAdditive_id r (MkRing r (+) (*) pfr))

|||Proof that 0*a = 0
Zmultleft: (r: Type) -> (pfr: Ring r) -> (a: r) -> ((Ring_Mult r pfr (DPair.fst(RingAdditive_id r pfr)) a) = (DPair.fst(RingAdditive_id r pfr)))
Zmultleft r (MkRing r (+) (*) pfr) a = (aplusaZ r (MkRing r (+) (*) pfr) (z*a) (
    trans (sym (pfd a z z)) (cong {f= \p => p*a} (pfz z))
  ) ) where
  z: r
  z = (DPair.fst(RingAdditive_id r (MkRing r (+) (*) pfr)))
  pfz: (a: r) -> (a+z=a)
  pfz a = Basics.fst ((DPair.snd (RingAdditive_id r (MkRing r (+) (*) pfr))) a)
  pfd: (a: r) -> (b: r) -> (c: r) -> ((b+c)*a = (b*a) + (c*a))
  pfd a b c = Basics.snd ((Basics.snd (Basics.snd pfr)) a b c)

|||Proof that a*0 = 0
Zmultright: (r: Type) -> (pfr: Ring r) -> (a: r) -> ((Ring_Mult r pfr a (DPair.fst(RingAdditive_id r pfr))) = (DPair.fst(RingAdditive_id r pfr)))
Zmultright r (MkRing r (+) (*) pfr) a = (aplusaZ r (MkRing r (+) (*) pfr) (a*z) (
    trans (sym (pfd a z z)) (cong {f= \p => a*p} (pfz z))
    ) ) where
    z: r
    z = (DPair.fst(RingAdditive_id r (MkRing r (+) (*) pfr)))
    pfz: (a: r) -> (a+z=a)
    pfz a = Basics.fst ((DPair.snd (RingAdditive_id r (MkRing r (+) (*) pfr))) a)
    pfd: (a: r) -> (b: r) -> (c: r) -> (a*(b+c) = (a*b) + (a*c))
    pfd a b c = Basics.fst ((Basics.snd (Basics.snd pfr)) a b c)
