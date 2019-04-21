module ZZplus

import congruence
import Quotient_Type
import ZZ_alt
import Product_Type_Eq

%access public export
%default total

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
         
    pf11 : (plus (plus a1 c2) (plus b1 d2) = plus (plus a2 c1) (plus b1 d2))
         = congruence Nat Nat (plus a1 c2) (plus a2 c1) (\x => (plus x (plus b1 d2))) pf_ac
    
    pf12 : (plus (plus a2 c1) (plus b1 d2) = plus (plus a2 c1) (plus b2 d1))
         = congruence Nat Nat (plus b1 d2) (plus b2 d1) (\x => (plus (plus a2 c1) x)) pf_bd
         
    pf13 : (plus (plus a2 c1) (plus b2 d1) = plus a2 (plus c1 (plus b2 d1)))
         = sym (plusAssociative a2 c1 (plus b2 d1))
         
    pf14 : (plus c1 (plus b2 d1) = plus (plus b2 d1) c1)
         = plusCommutative c1 (plus b2 d1)
         
    pf15 : (plus (plus b2 d1) c1 = plus b2 (plus d1 c1))
         = sym (plusAssociative b2 d1 c1)
    
    pf16 : (plus c1 (plus b2 d1) = plus b2 (plus d1 c1))
         = trans pf14 pf15     
                   
    pf17 : (plus a2 (plus c1 (plus b2 d1)) = plus a2 (plus b2 (plus d1 c1)))
         = congruence Nat Nat (plus c1 (plus b2 d1)) (plus b2 (plus d1 c1)) (\x => (plus a2 x)) pf16
         
    pf18 : (plus a2 (plus b2 (plus d1 c1)) = plus (plus a2 b2) (plus d1 c1))
         = plusAssociative a2 b2 (plus d1 c1) 
         
    pf19 : (plus (plus a2 b2) (plus d1 c1) = plus (plus a2 b2) (plus c1 d1))
         = congruence Nat Nat (plus d1 c1) (plus c1 d1) (\x => (plus (plus a2 b2) x)) (plusCommutative d1 c1)                       
        
    pf20 = trans (trans (trans (trans (trans (trans pf10 pf11) pf12) pf13) pf17) pf18) pf19
        
    in
    pf20
    
isZero : (a : ZZ1) -> Type
isZero a = (n : ZZ1) -> (ZZ_Rel (plus n a)  n)

||| A proof that if a is zero then it is of the form (n,n)
ZZ_property1 : (a : ZZ1) -> (isZero a) -> (n : Nat ** (ZZ_Rel a (n,n)))
ZZ_property1 (a,b) pfZ = (Z ** (pfZ (Z,Z)))

||| A proof that if any element of the form (n,n) is a zero element
ZZ_property2 : (n : Nat) -> (isZero (n,n))
ZZ_property2 n (a, b) = let
    
    pf1 : (plus a n = plus n a)
        = plusCommutative a n
    
    pf2 : (plus (plus a n) b = plus (plus n a) b)
        = congruence Nat Nat (plus a n) (plus n a) (\c => (plus c b)) pf1

    pf3 : (plus n (plus a b) = plus (plus n a) b)
        = plusAssociative n a b
        
    pf4 : (plus (plus a n) b = plus n (plus a b))
        = trans pf2 (sym pf3)
        
    pf5 : (plus a b = plus b a)
        = plusCommutative a b  
        
    pf6 : (plus n (plus a b) = plus n (plus b a))
        = congruence Nat Nat (plus a b) (plus b a) (\c => (plus n c)) pf5
        
    pf7 : (plus n (plus b a) = plus (plus n b) a)
        = plusAssociative n b a                  
        
    pf8 : (plus n b = plus b n)
        = plusCommutative n b
        
    pf9 : (plus (plus n b) a = plus (plus b n) a)
        = congruence Nat Nat (plus n b) (plus b n) (\c => (plus c a)) pf8
        
    pf10 : (plus n (plus b a) = plus (plus b n) a)
         = trans pf7 pf9            
         
    pf11 : (plus n (plus a b) = plus (plus b n) a)
         = trans pf6 pf10  
         
    pf12 : (plus (plus a n) b = plus (plus b n) a)
         = trans pf4 pf11     
         
    in
    pf12
    
    
    
    
    
    
    
    
    
    
    
    
    
    


