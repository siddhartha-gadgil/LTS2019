module Cosets

import Group
%access public export
--The type of proofs that a type trav traverses a given coset only once, if at all
CosetInj: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (f: trav -> g) -> Type
CosetInj  h (+) pf1 g (*) pf2 sbgrp trav f = ((x: trav) -> (y: trav) -> (p: h ** (f x) = (incl p)*(f y)) -> (x = y)) where
  incl = (fst sbgrp)

--The type of proofs that a type trav traverses every coset of a given group g wrt a subgroup h
CosetAll: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (f: trav -> g) -> Type
CosetAll h (+) pf1 g (*) pf2 sbgrp trav f = ((a: g) -> (p: h ** (t: trav ** ((f t)*(incl p) = a)))) where
  incl = (fst sbgrp)

-- Traversal type - the type of proofs that a given type traverses each coset exactly once
IsTraversal: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> Type
IsTraversal h (+) pf1 g (*) pf2 sbgrp trav = DPair (trav -> g) (\f => (CosetInj h (+) pf1 g (*) pf2 sbgrp trav f, CosetAll h (+) pf1 g (*) pf2 sbgrp trav f))

--Defining the multiplication operation between elements of a traversal
MulTrav: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (IsTraversal h (+) pf1 g (*) pf2 sbgrp trav) -> trav -> trav -> trav
MulTrav h (+) pf1 g (*) pf2 sbgrp trav pftrav y z = (fst (snd ((snd (snd pftrav)) ((f y)*(f z))))) where
  f: trav -> g
  f = (fst pftrav)

--Proof of uniqueness of the coset representative in trav, in the following sense
--Proof that the operation that generates coset representative in trav for an element of g (from CosetAll) inverts the function generating a coset representative by going from trav to g (from IsTraversal)
corepfinv: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (pftrav: IsTraversal h (+) pf1 g (*) pf2 sbgrp trav) -> (y: trav) -> (((fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) )) ) = y)
corepfinv h (+) pf1 g (*) pf2 sbgrp trav pftrav y = (sym ((fst (snd pftrav)) y t (p ** (sym (snd (snd  ((snd (snd pftrav)) (f y)) )))) )) where
  t: trav
  t = (fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) ))
  f: trav -> g
  f = (fst pftrav)
  p: h
  p = (fst ((snd (snd pftrav)) (f y)))


--Proof that the definitional equality for traversal multiplication holds
MulTravDefPf: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (pftrav: IsTraversal h (+) pf1 g (*) pf2 sbgrp trav) -> (y: trav) -> (z: trav) -> (MulTrav h (+) pf1 g (*) pf2 sbgrp trav pftrav y z) = ((fst (snd ((snd (snd pftrav)) (((fst pftrav) y)*((fst pftrav) z))) )))
MulTravDefPf h (-) pf1 g (*) pf2 sbgrp trav pftrav y z = Refl

--Proof that the function from g to trav recovered from CosetAll is in some sense a magma homorphism
MulTravHomPf: (h: Type) -> ((+) : h -> h -> h) -> (pf1: IsGroup h (+)) -> (g: Type) -> ((*) : g -> g -> g) -> (pf2: IsGroup g (*)) -> (sbgrp: Subgroup h (+) pf1 g (*) pf2) -> (trav: Type) -> (pftrav: IsTraversal h (+) pf1 g (*) pf2 sbgrp trav) -> (y: trav) -> (z: trav) -> ((fst (snd ((snd (snd pftrav)) (((fst pftrav) y)*((fst pftrav) z))) ))) = (MulTrav h (+) pf1 g (*) pf2 sbgrp trav pftrav ((fst (snd ((snd (snd pftrav)) ((fst pftrav) y)) ))) ((fst (snd ((snd (snd pftrav)) ((fst pftrav) z)) ))))
MulTravHomPf h (-) pf1 g (*) pf2 sbgrp trav pftrav y z = trans (sym (MulTravDefProof)) (trans (cong {f = f1} (sym CorepFInverseY)) (cong {f = f2} (sym CorepFInverseZ))) where

  MulTravDefProof: (MulTrav h (-) pf1 g (*) pf2 sbgrp trav pftrav y z) = ((fst (snd ((snd (snd pftrav)) (((fst pftrav) y)*((fst pftrav) z))) )))
  MulTravDefProof = (MulTravDefPf h (-) pf1 g (*) pf2 sbgrp trav pftrav y z )

  f1: trav -> trav
  f1 x = MulTrav h (-) pf1 g (*) pf2 sbgrp trav pftrav x z

  f2: trav -> trav
  f2 x = MulTrav h (-) pf1 g (*) pf2 sbgrp trav pftrav ((fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) )) ) x

  CorepFInverseY: (((fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) )) ) = y)
  CorepFInverseY = CorepFInv h (-) pf1 g (*) pf2 sbgrp trav pftrav y

  CorepFInverseZ: (((fst (snd ((snd (snd pftrav)) ((fst pftrav) z) ) )) ) = z)
  CorepFInverseZ = CorepFInv h (-) pf1 g (*) pf2 sbgrp trav pftrav z
