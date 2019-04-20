module RingProperties

import Ring
import Monoid
import Group
import Group_property

%access public export

|||Auxiliary function that provzs that if a+a=a thzn a=0
total
aplusaZ: (r: Type) -> (pfr: Ring r) -> (a: r) -> ((Ring_Add r pfr a a) =a) -> (a = (DPair.fst(RingAdditive_id r pfr)))
aplusaZ r (MkRing r (+) (*) pfr) a prf = (Group_property_4 r (+) (Basics.fst (Basics.fst pfr)) a a z (trans prf (sym (Basics.fst (pfz a))) )) where
  z: r
  z = (DPair.fst(RingAdditive_id r (MkRing r (+) (*) pfr)))
  pfz: (a: r) -> (a+z=a, z+a=a)
  pfz = DPair.snd (RingAdditive_id r (MkRing r (+) (*) pfr))

|||Proof that 0*a = 0
total
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
total
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

|||Proof that for a ring homomorphism f between rings with identity, f(0) = 0
total
RHomZtoZ: (r1: Type) -> (pf1: Ring r1) -> (r2: Type) -> (pf2: Ring r2) -> (f: r1 -> r2) -> RHom r1 pf1 r2 pf2 f -> f(fst(RingAdditive_id r1 pf1)) = fst (RingAdditive_id r2 pf2)
RHomZtoZ r1 (MkRing r1 ((+)) (m) pf1) r2 (MkRing r2 (*) m1 pf2) f pfhom = aplusaZ r2 (MkRing r2 (*) m1 pf2) (f z1) (
    trans
    (sym (Basics.fst(pfhom z1 z1)))
    (cong (Basics.fst(pfid1 z1)))
    ) where
  z1: r1
  z1 = fst(RingAdditive_id r1 (MkRing r1 ((+)) (m) pf1))
  pfid1: (a : r1) -> ((a+z1) = a, (z1+a) = a)
  pfid1 = snd(RingAdditive_id r1 (MkRing r1 ((+)) (m) pf1))

|||Proof that for a ring homomorphism f, f(0) = 0
total
IRHomZtoZ: (r1: Type) -> (pf1: Ring_with_identity r1) -> (r2: Type) -> (pf2: Ring_with_identity r2) -> (f: r1 -> r2) -> IRHom r1 pf1 r2 pf2 f -> f(fst(RingAdditive_id r1 (Ring_with_identity_isRing r1 pf1))) = fst (RingAdditive_id r2 (Ring_with_identity_isRing r2 pf2))
IRHomZtoZ r1 (MkRing_with_identity r1 ((((+)))) (m) (a, b)) r2 (MkRing_with_identity r2 (((*))) (m1) (a', b')) f pfhom = aplusaZ r2 prf2 (f z1) (
    trans
    (sym (Basics.fst(pfhom z1 z1)))
    (cong (Basics.fst(pfid1 z1)))
    ) where
  prf1: Ring r1
  prf1 = MkRing r1 (+) (m) (a, ((Basics.fst (Basics.fst b)), (Basics.snd b)))
  prf2: Ring r2
  prf2 = MkRing r2 (*) (m1) (a', ((Basics.fst (Basics.fst b')), (Basics.snd b')))
  z1: r1
  z1 = fst(RingAdditive_id r1 prf1)
  pfid1: (a : r1) -> ((a + z1) = a, (z1 + a) = a)
  pfid1 a = snd(RingAdditive_id r1 prf1) a
