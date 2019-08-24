module ZZsubs

import congruence
import Quotient_Type
import ZZ_alt
import Product_Type_Eq
import ZZplus

%access public export
%default total

negate : ZZ1 -> ZZ1
negate (a, b) = (b, a)

negatePassesThrough : (a, b : ZZ1) -> (ZZ_Rel a b) -> (ZZ_Rel (negate a) (negate b))
negatePassesThrough (a1, a2) (b1, b2) pfRel = sym pfRel

subs : ZZ1 -> ZZ1 -> ZZ1
subs a b = plus a (negate b)

subsPassesThrough : (a, b, c, d : ZZ1) -> (ZZ_Rel a c) -> (ZZ_Rel b d) ->
                    (ZZ_Rel (subs a b) (subs c d))

subsPassesThrough a b c d pfac pfbd = let
    
    pf1 : (ZZ_Rel (negate b) (negate d))
        = negatePassesThrough b d pfbd
    
    pf2 : (ZZ_Rel (plus a (negate b)) (plus c (negate d)))
        = plusPassesThrough a (negate b) c (negate d) pfac pf1
    
    in
    pf2

