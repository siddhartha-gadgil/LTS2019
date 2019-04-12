module Rats

import ZZ
import ZZUtils
import Rationals

data Rats : Type where
  Rat : (p : ZZ) -> (q: ZZ) -> (NotZero q) -> Rats

add : Rats -> Rats -> Rats
add (Rat p q x) (Rat y z w) =
  let
    num = (p * z) + (q * y)
    den = q * z
    pf : NotZero den = productNonZero x w
  in
    Rat num den pf
