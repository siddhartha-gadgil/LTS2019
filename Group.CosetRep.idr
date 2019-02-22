module CosetRep

import Group
import Cosets
%access public export

--Generates (equivalent) representatives of the image in g of a
--coset (element of the transversal type) in the transversal type
repgen: (trav: Type) -> Transversal trav -> (y: trav) -> trav
repgen trav (MkTransversal h (MkGroup h (+) pfh) g (MkGroup g (*) pfg) sbgrp trav pftrav) y = (fst (snd ((snd (snd pftrav)) (f y) ) )) where
    f: trav -> g
    f = fst pftrav
    incl: h->g
    incl = fst sbgrp

--Proof of uniqueness of the coset representative in trav, in the following sense
--Proof that the operation that generates coset representative in trav for an
--element of g (from CosetAll) inverts the function generating a coset representative by going from trav to g (from IsTraversal)
CorepFinv: (trav: Type) -> (pft: Transversal trav) -> (y: trav) -> (repgen trav pft y = y)
CorepFinv  trav (MkTransversal h (MkGroup h (+) pfh) g (MkGroup g (*) pfg) sbgrp trav pftrav)
  y = (sym (
  (Basics.fst (DPair.snd pftrav)) y rep (p ** (sym (DPair.snd (DPair.snd  ((Basics.snd (DPair.snd pftrav)) (f y)) ))))
  )) where
  rep: trav
  rep = (fst (snd ((snd (snd pftrav)) ((fst pftrav) y) ) ))
  f: trav -> g
  f = (fst pftrav)
  p: h
  p = (fst ((snd (snd pftrav)) (f y)))
  
