module ZZplus

import congruence
import Quotient_Type
import ZZ_alt
import Product_Type_Eq

plus : ZZ1 -> ZZ1 -> ZZ1
plus (a, b) (c, d) = (plus a c, plus b d)

plusCommutative : (n, m : ZZ1) -> (plus n m = plus m n)
plusCommutative (a, b) (c, d) = let
    
    pf1 : (plus a c = plus c a) 
        = plusCommutative a c
    
    pf2 : (plus b d = plus d b)
        = plusCommutative b d
    
    in
    (Product_Eq_property_1 Nat Nat (plus (a, b) (c, d)) (plus (c, d) (a, b)) pf1 pf2)


