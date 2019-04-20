module GroupCosets

import Group

%access public export

--The type of proofs that a type trav Transverses a given coset only once,
--if at all
total
CosetInj: (h: Type) -> (pfh: Group h) -> (g: Type) -> (pfg: Group g) ->
          (sbgrp: Subgroup h pfh g pfg) ->
          (trav: Type) -> (f: trav -> g) -> Type
CosetInj  h (MkGroup h (+) pfh) g (MkGroup g (*) pfg) sbgrp trav f =
  ((x: trav) -> (y: trav) ->
  (p: h ** (f x) = (incl p)*(f y)) -> (x = y)) where
  incl = (fst sbgrp)

--The type of proofs that a type trav Transverses every coset of a given
-- group g wrt a subgroup h
total
CosetAll: (h: Type) -> (pfh: Group h) -> (g: Type) -> (pfg: Group g) ->
          (sbgrp: Subgroup h pfh g pfg) ->
          (trav: Type) -> (f: trav -> g) -> Type
CosetAll h (MkGroup h (+) pfh) g (MkGroup g (*) pfg) sbgrp trav f =
  ((a: g) ->
  (p: h ** (t: trav ** ((incl p)*(f t) = a)))) where
  incl = (DPair.fst sbgrp)

-- Transversal type - the type of proofs that a given type is a Transversal
-- of a group g wrt a subgroup h
total
IsTransversal: (h: Type) -> (pfh: Group h) -> (g: Type) -> (pfg: Group g) ->
               (sbgrp: Subgroup h pfh g pfg) -> (trav: Type) -> Type
IsTransversal h pfh g pfg sbgrp trav = DPair (trav -> g) (\f =>
  (CosetInj h pfh g pfg sbgrp trav f,
  CosetAll  h pfh g pfg sbgrp trav f)
  )

--The transversal data type
data Transversal: (trav: Type) -> Type where
  MkTransversal: (h: Type) -> (pfh: Group h) -> (g: Type) -> (pfg: Group g) ->
                 (sbgrp: Subgroup h pfh g pfg) -> (trav: Type) ->
                 (IsTransversal h pfh g pfg sbgrp trav) -> Transversal trav

--Defining the multiplication operation between elements of a traversal
total
MulTrans: (trav: Type) -> (Transversal trav) -> trav -> trav -> trav
MulTrans trav (MkTransversal h (MkGroup h (+) pfh) g (MkGroup g (*) pfg) sbgrp trav pftrav) y z = (DPair.fst (DPair.snd ((Basics.snd (DPair.snd pftrav)) ((f y)*(f z))))) where
  f: trav -> g
  f = (DPair.fst pftrav)

