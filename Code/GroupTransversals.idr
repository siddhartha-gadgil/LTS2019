module Transversals

import Group
import GroupCosets
import GroupCosetRep
%access public export

--Proof that the definitional equality for Transversal multiplication holds
MulTransDefPf: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) ->
                (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) ->
                (sbgrp: Subgroup h (MkGroup h (+) pf1) g (MkGroup g (*) pf2)) -> (trav: Type) ->
                (pftrav: IsTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav) -> (y: trav) -> (z: trav) ->
                (MulTrans trav (MkTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav pftrav) y z) =
                  ((DPair.fst (DPair.snd ((Basics.snd (DPair.snd pftrav)) (((DPair.fst pftrav) y)*((DPair.fst pftrav) z))) )))
MulTransDefPf h (+) pf1 g (*) pf2 sbgrp trav pftrav y z = Refl

--Proof that the function from g to trav recovered from CosetAll is in some sense a magma homorphism
MulTransHomPf: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) ->
                (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) ->
                (sbgrp: Subgroup h (MkGroup h (+) pf1) g (MkGroup g (*) pf2)) -> (trav: Type) ->
                (pftrav: IsTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav) -> (y: trav) -> (z: trav) ->
                ((DPair.fst (DPair.snd ((Basics.snd (DPair.snd pftrav)) (((DPair.fst pftrav) y)*((DPair.fst pftrav) z))) ))) = (MulTrans trav (MkTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav pftrav) ((DPair.fst (DPair.snd ((Basics.snd (DPair.snd pftrav)) (((DPair.fst pftrav) y))) ))) ((DPair.fst (DPair.snd ((Basics.snd (DPair.snd pftrav)) (((DPair.fst pftrav) z))) ))))
MulTransHomPf h (+) pf1 g (*) pf2 sbgrp trav pftrav y z = trans (sym (MulTravDefProof)) (trans (cong {f = f1} (sym CorepFInverseY)) (cong {f = f2} (sym CorepFInverseZ))) where

  MulTravDefProof: (MulTrans trav (MkTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav pftrav) y z) = ((fst (snd ((snd (snd pftrav)) (((fst pftrav) y)*((fst pftrav) z))) )))
  MulTravDefProof = (MulTransDefPf h (+) pf1 g (*) pf2 sbgrp trav pftrav y z )

  f1: trav -> trav
  f1 x = MulTrans trav (MkTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav pftrav) x z

  f2: trav -> trav
  f2 x = MulTrans trav (MkTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav pftrav) ((DPair.fst (DPair.snd ((Basics.snd (DPair.snd pftrav)) (((DPair.fst pftrav) y) ) )) )) x

  CorepFInverseY: (((fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) )) ) = y)
  CorepFInverseY = CorepFinv trav (MkTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav pftrav) y

  CorepFInverseZ: (((fst (snd ((snd (snd pftrav)) ((fst pftrav) z) ) )) ) = z)
  CorepFInverseZ = CorepFinv trav (MkTransversal h (MkGroup h (+) pf1) g (MkGroup g (*) pf2) sbgrp trav pftrav) z
