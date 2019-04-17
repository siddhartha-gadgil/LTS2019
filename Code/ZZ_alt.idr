module ZZ_alt

import congruence
import Quotient_Type

%access public export
%default total

ZZ1 : Type
ZZ1 = (Nat, Nat)	
	
ZZ_Rel : (Nat, Nat) -> (Nat, Nat) -> Type
ZZ_Rel (a, b) (c, d) = ( (plus a d) = (plus b c) )

IsRefl_ZZ_Rel : (n : ZZ1) -> (ZZ_Rel n n)
IsRefl_ZZ_Rel (a, b) = (plusCommutative a b)

IsSym_ZZ_Rel : (n, m : ZZ1) -> (ZZ_Rel n m) -> (ZZ_Rel m n)
IsSym_ZZ_Rel (a, b) (c, d) pf_rel = (rewrite (plusCommutative d a) in 
                                    (rewrite (plusCommutative c b) in (sym pf_rel)))

congruence_1 : (ty1 : Type) -> (ty2 : Type) -> (a, b, c, d : ty1) -> 
               (f : ty1 -> ty1 -> ty2) -> (a = b) -> (c = d) -> ( (f a c) = (f b d) )
               
congruence_1 ty1 ty2 a a c c f Refl Refl = Refl

succCancellation : (a, b : Nat) -> ( (S a) = (S b) ) -> (a = b)
succCancellation a a Refl = Refl

plusCancellation_left : (a, b, c : Nat) -> ( (plus c a) = (plus c b) ) -> (a = b)

plusCancellation_left a b Z pf = pf

plusCancellation_left a b (S k) pf = let
    
    pf1 : (plus k a = plus k b)
        = succCancellation (plus k a) (plus k b) pf
    in

    (plusCancellation_left a b k pf1)


plusCancellation_right : (a, b, c : Nat) -> ( (plus a c) = (plus b c) ) -> (a = b)

plusCancellation_right a b Z pf = (rewrite (plusCommutative Z b) in 
                            (rewrite (plusCommutative Z a) in pf))
                            
plusCancellation_right a b (S k) pf = let
    
    pf1 : ( plus a (S k) = S (plus k a) ) 
        = plusCommutative a (S k)
        
    pf2 : ( plus b (S k) = S (plus k b) )
        = ( plusCommutative b (S k))
        
    pf3 : ( S (plus k a) = S (plus k b) )
        = trans (sym pf1) (trans pf pf2)    
    in
    (plusCancellation_left a b (S k) pf3)	

IsTrans_ZZ_Rel : (a, b, c : ZZ1) -> (ZZ_Rel a b) -> (ZZ_Rel b c) -> (ZZ_Rel a c)
IsTrans_ZZ_Rel (a, b) (c, d) (k, l) pf1 pf2 = let
    
    pf3 : (plus (plus a d) (plus c l) = plus (plus b c) (plus d k)) 
        = congruence_1 Nat Nat (plus a d) (plus b c) (plus c l) (plus d k) plus pf1 pf2
    
    pf4 : (plus a (plus d (plus c l)) = plus (plus a d) (plus c l)) 
        = plusAssociative a d (plus c l)
        
    pf5 : (plus b (plus c (plus d k)) = plus (plus b c) (plus d k))
        = plusAssociative b c (plus d k)    
        
    pf6 : (plus c l = plus l c)
        = plusCommutative c l
        
    pf7 : (plus d (plus c l) = plus d (plus l c))
        = congruence Nat Nat (plus c l) (plus l c) (\x => (plus d x)) pf6
        
    pf8 : (plus d (plus l c) = plus (plus d l) c)
        = plusAssociative d l c 
        
    pf9 : (plus d (plus c l) = plus (plus d l) c)
        = trans pf7 pf8
        
    pf10 : (plus d l = plus l d)
         = plusCommutative d l
         
    pf11 : (plus (plus d l) c = plus (plus l d) c)
         = congruence Nat Nat (plus d l) (plus l d) (\x => (plus x c)) pf10                 
    
    pf12 : ( plus d (plus l c) = plus (plus l d) c )
         = trans pf8 pf11
         
    pf13 : (plus d (plus c l) = plus (plus l d) c)
         = trans pf7 pf12
    
    pf14 : (plus l (plus d c) = plus (plus l d) c)
         = plusAssociative l d c          
         
    pf15 : ( plus (plus d l) c = plus l (plus d c) )
         = trans pf11 (sym pf14)
         
    pf16 : (plus d (plus c l) = plus l (plus d c))
         = trans pf9 pf15
         
    pf17 : (plus a (plus d (plus c l)) = plus a (plus l (plus d c)))
         = congruence Nat Nat (plus d (plus c l)) (plus l (plus d c)) (\x => (plus a x)) pf16               
    
    pf18 : (plus a (plus l (plus d c)) = plus (plus a l) (plus d c))
         = plusAssociative a l (plus d c)
    
    pf19 : (plus (plus a d) (plus c l) = plus (plus a l) (plus d c))
         = trans (trans (sym pf4) pf17) pf18
    
    pf20 : ( plus d k = plus k d )
         = plusCommutative d k
         
    pf21 : ( plus c (plus d k) = plus c (plus k d) )
         = congruence Nat Nat (plus d k) (plus k d) (\x => (plus c x)) pf20 
         
    pf22 : ( plus c (plus k d) = plus (plus c k) d )
         = plusAssociative c k d

    pf23 : (  plus c k = plus k c )
         = plusCommutative c k
         
    pf24 : ( plus (plus c k) d = plus (plus k c) d )
         = congruence Nat Nat (plus c k) (plus k c) (\x => (plus x d)) pf23          
    
    pf25 : ( plus (plus k c) d = plus k (plus c d) )
         = sym (plusAssociative k c d)
         
    pf26 : ( plus c (plus d k) = plus k (plus c d) ) 
         = trans pf21 (trans pf22 (trans pf24 pf25))
         
    pf27 : ( plus b (plus c (plus d k)) = plus b (plus k (plus c d)) )
         = congruence Nat Nat (plus c (plus d k)) (plus k (plus c d)) (\x => (plus b x)) pf26  
         
    pf28 : ( plus b (plus k (plus c d)) = plus (plus b k) (plus c d) )
         = plusAssociative b k (plus c d)           
         
    pf29 : ( plus c d = plus d c )
         = plusCommutative c d
         
    pf30 : ( plus (plus b k) (plus c d) = plus (plus b k) (plus d c) )
         = congruence Nat Nat (plus c d) (plus d c) (\x => (plus (plus b k) x)) pf29          
    
    pf31 : ( plus b (plus c (plus d k)) = plus (plus b k) (plus d c) )
         = (trans (trans pf27 pf28) pf30)
         
    pf32 : ( plus (plus b c) (plus d k) = plus (plus b k) (plus d c) )
         = trans (sym pf5) pf31
         
    pf33 : ( plus (plus a l) (plus d c) = plus (plus b k) (plus d c) )
         = trans (trans (sym pf19) pf3) pf32 
                            
    in
    (plusCancellation_right (plus a l) (plus b k) (plus d c) pf33)
    
ZZ_Rel_is_EqRel : IsEqRel ZZ1 ZZ_Rel
ZZ_Rel_is_EqRel = (IsRefl_ZZ_Rel, (IsSym_ZZ_Rel, IsTrans_ZZ_Rel))

ZZ_Quotient : (Quotient_Type ZZ1 ZZ_Rel)
ZZ_Quotient = Cons_quotient_Type ZZ_Rel_is_EqRel    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
