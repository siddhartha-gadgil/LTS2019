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
    
plusPassesThrough : (a, b, c, d : ZZ1) -> (ZZ_Rel a c) -> (ZZ_Rel b d) ->
                    (ZZ_Rel (plus a b) (plus c d))
                    
plusPassesThrough (a1, a2) (b1, b2) (c1, c2) (d1, d2) pf_ac pf_bd = let
    
    pf1 : (plus (plus a1 b1) (plus c2 d2) = plus a1 (plus b1 (plus c2 d2)))
        = (sym (plusAssociative a1 b1 (plus c2 d2)))
        
    pf2 : (plus b1 (plus c2 d2) = plus (plus b1 c2) d2)
        = (plusAssociative b1 c2 d2)
        
    pf3 : ((plus a1 (plus b1 (plus c2 d2))) = (plus a1 (plus (plus b1 c2) d2)))  
        = congruence Nat Nat (plus b1 (plus c2 d2)) (plus (plus b1 c2) d2) (\x => (plus a1 x)) pf2
        
    pf4 : (plus a1 (plus (plus b1 c2) d2) = plus (plus a1 (plus b1 c2)) d2)
        = plusAssociative a1 (plus b1 c2) d2
        
    pf5 : (plus b1 c2 = plus c2 b1)
        = (plusCommutative b1 c2)  
        
    pf6 : (plus (plus a1 (plus b1 c2)) d2 = plus (plus a1 (plus c2 b1)) d2)
        = congruence Nat Nat (plus b1 c2) (plus c2 b1) (\x => (plus (plus a1 x) d2)) pf5
        
    pf7 : (plus a1 (plus c2 b1) = plus (plus a1 c2) b1)
        = plusAssociative a1 c2 b1                     
        
    pf8 : (plus (plus a1 (plus c2 b1)) d2 = plus (plus (plus a1 c2) b1) d2)
        = congruence Nat Nat (plus a1 (plus c2 b1)) (plus (plus a1 c2) b1) (\x => (plus x d2)) pf7    
        
    pf9 : (plus (plus (plus a1 c2) b1) d2 = plus (plus a1 c2) (plus b1 d2))
        = sym (plusAssociative (plus a1 c2) b1 d2) 
        
    pf10 : (plus (plus a1 b1) (plus c2 d2) = plus (plus a1 c2) (plus b1 d2)) -- one part 
         = trans (trans (trans (trans (trans pf1 pf3) pf4) pf6) pf8) pf9       
         
         
        
    in
    ?rhs


