module Module

import Monoid
import Group
import Ring
import Group_property
import NatUtils

--(modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) ->
-- ((*) : ring -> ring -> ring) -> (IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
--This just the data required for a module, the set modu and a ring. So, this big chunk of code will appear everywhere

|||Type of operation between a ring and a moduule that distributes over addition of the ring
total
dotDistributesOverRing : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring)
                          -> ((*) : ring -> ring -> ring) -> (IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu) -> Type
dotDistributesOverRing modu ring (+) (++) (*) prfRing (.) = (r : ring) -> (s : ring) -> (m : modu) -> ((r ++ s) . m = (r . m) + (s . m))

|||Type of operation between a ring and a moduuule that distributes over addition of the Module
total
dotDistributesOverModule : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring)
                            -> ((*) : ring -> ring -> ring) -> (IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu) -> Type
dotDistributesOverModule modu ring (+) (++) (*) prfRing (.) = (m : modu) -> (n : modu) -> (r : ring) -> (r . (m + n) = (r . m) + (r . n))

|||Type of operation that respects ring multiplication
total
dotRespectsRingMult : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                       -> (IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu) -> Type
dotRespectsRingMult modu ring (+) (++) (*) prfRing (.) = (r : ring) -> (s : ring) -> (m : modu) -> ((r*s) . m = r . (s . m))

|||Type of operation that maps 1.m to m.
total
dotRespectsIdentity : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                        -> (IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu) -> Type
dotRespectsIdentity modu ring (+) (++) (*) prfRing (.) = (m : modu) -> (e . m = m) where
                                                                              e = fst (snd (fst (snd prfRing)))
|||The type of a Module. As the operations on the set modu determines it's abelianess property, we should only include the operation on the set modu and the operation between the set modu and the ring
total
IsleftModule : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                -> (IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu) -> Type
IsleftModule modu ring (+) (++) (*) prfRing (.) = ((IsAbelianGrp modu (+)) , (dotRespectsIdentity modu ring (+) (++) (*) prfRing (.) , (dotDistributesOverRing modu ring (+) (++) (*) prfRing (.) , ( dotDistributesOverModule modu ring (+) (++) (*) prfRing (.) , dotRespectsRingMult modu ring (+) (++) (*) prfRing (.)))))

--Below are a bunch of auxiliary functions to get recover dot distributing over blah from the envelope Type IsleftModule

|||Gives the Abelian Group property of a module
total
AbelianAddition : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                    -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                    -> (IsleftModule modu ring (+) (++) (*) prfRing (.)) -> (IsAbelianGrp modu (+))
AbelianAddition modu ring (+) (++) (*) prfRing (.) prfLeftModule = fst (prfLeftModule)

|||Gives the Zero of the Module
total
ZeroOfModule : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                 -> (IsleftModule modu ring (+) (++) (*) prfRing (.)) -> (e : modu ** ((a : modu) -> (a + e = a , e + a = a)))
ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule = fst (snd (fst (fst (prfLeftModule))))

|||Gives the dot distributes over Ring addition property of the module
total
dotOverRingAdd : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                  -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                   -> (IsleftModule modu ring (+) (++) (*) prfRing (.)) -> dotDistributesOverRing modu ring (+) (++) (*) prfRing (.)
dotOverRingAdd modu ring (+) (++) (*) prfRing (.) prfLeftModule = fst (snd (snd (prfLeftModule)))

|||Gives the dot distributes over module addition property of the module
total
dotOverModuleAdd : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                    -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                     -> (IsleftModule modu ring (+) (++) (*) prfRing (.)) -> dotDistributesOverModule modu ring (+) (++) (*) prfRing (.)
dotOverModuleAdd modu ring (+) (++) (*) prfRing (.) prfLeftModule = fst (snd (snd (snd (prfLeftModule))))

|||Gives the dot Associates with ring multiplication property of the module
total
dotAssociatesRingMult : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                        -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                         -> (IsleftModule modu ring (+) (++) (*) prfRing (.)) -> dotRespectsRingMult modu ring (+) (++) (*) prfRing (.)
dotAssociatesRingMult modu ring (+) (++) (*) prfRing (.) prfLeftModule = snd (snd (snd (snd (prfLeftModule))))

|||Gives the dot Associates with ring multiplication property of the module
total
dotRingIdentity : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                    -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                     -> (IsleftModule modu ring (+) (++) (*) prfRing (.)) -> dotRespectsIdentity modu ring (+) (++) (*) prfRing (.)
dotRingIdentity modu ring (+) (++) (*) prfRing (.) prfLeftModule = fst (snd (prfLeftModule))

|||Proof that r*0 = 0 for all r in the underlying ring
total
RingMultZeroEqualsZero : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                          -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                           -> (prfLeftModule : IsleftModule modu ring (+) (++) (*) prfRing (.))
                            -> ((r : ring) -> (r . (fst (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule)) = (fst (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule))))
RingMultZeroEqualsZero modu ring (+) (++) (*) prfRing (.) prfLeftModule = k where
                                                                              e : modu
                                                                              e = fst (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule)
                                                                              u : ring -> modu -> modu
                                                                              u r m = r . m
                                                                              f : (r : ring) -> (r . (e + e) = (r . e) + (r . e))
                                                                              f r = (dotOverModuleAdd modu ring (+) (++) (*) prfRing (.) prfLeftModule e e r)
                                                                              g : (r : ring) -> (r . (e + e) = r . e)
                                                                              g r = (cong (fst ((snd (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule)) e)))
                                                                              h : (r : ring) -> (r . e = (r . e) + (r . e))
                                                                              h r = (trans (sym (g r)) (f r))
                                                                              i : (r : ring) -> ((r . e) + e = (r . e))
                                                                              i r = (fst ((snd (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule)) (r . e)))
                                                                              j : (r : ring) -> ((r . e) + e = (r . e) + (r . e))
                                                                              j r = (trans (i r) (h r))
                                                                              k : (r : ring) -> ((r . e) = e)
                                                                              k r = (sym (Group_property_4 modu (+) (fst (fst prfLeftModule)) (r . e) e (r . e) (j r)))

|||Proof that 0*m = 0 for m in the module
total
ZeroMultModuleEqualsZero : (modu : Type) -> (ring : Type) -> ((+) : modu -> modu -> modu) -> ((++) : ring -> ring -> ring) -> ((*) : ring -> ring -> ring)
                            -> (prfRing : IsRing_with_identity ring (++) (*)) -> ((.) : ring -> modu -> modu)
                             -> (prfLeftModule : IsleftModule modu ring (+) (++) (*) prfRing (.))
                              -> ((m : modu) -> ((fst (fst (snd (fst (fst prfRing))))) . m = fst (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule)))
ZeroMultModuleEqualsZero modu ring (+) (++) (*) prfRing (.) prfLeftModule = k where
                                                                                        e : modu
                                                                                        e = fst (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule)
                                                                                        z : ring
                                                                                        z = fst (fst (snd (fst (fst prfRing))))
                                                                                        u : modu -> ring -> modu
                                                                                        u m r = r . m
                                                                                        f : (m : modu) -> ((z ++ z) . m = (z . m) + (z . m))
                                                                                        f m = (dotOverRingAdd modu ring (+) (++) (*) prfRing (.) prfLeftModule z z m)
                                                                                        g : (m : modu) -> ((z ++ z) . m = z . m)
                                                                                        g m = (functionExtendsEquality2 ring modu (u m) (z ++ z) z (fst (snd (fst (snd (fst (fst prfRing)))) z)))
                                                                                        h : (m : modu) -> (z . m = (z . m) + (z . m))
                                                                                        h m = (trans (sym (g m)) (f m))
                                                                                        i : (m : modu) -> ((z . m) + e = (z . m))
                                                                                        i m = (fst ((snd (ZeroOfModule modu ring (+) (++) (*) prfRing (.) prfLeftModule)) (z . m)))
                                                                                        j : (m : modu) -> ((z . m) + e = (z . m) + (z . m))
                                                                                        j m = (trans (i m) (h m))
                                                                                        k : (m : modu) -> ((z . m) = e)
                                                                                        k m = (sym (Group_property_4 modu (+) (fst (fst prfLeftModule)) (z . m) e (z . m) (j m)))
