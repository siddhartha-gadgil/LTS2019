module ZZ_alt

import congruence

%access public export
%default total

ZZ1 : Type
ZZ1 = (Nat, Nat)
	
ZZ_Rel : (Nat, Nat) -> (Nat, Nat) -> Type
ZZ_Rel (a, b) (c, d) = ( (mult a d) = (mult b c) )

IsRefl_ZZ_Rel : (n : ZZ1) -> (ZZ_Rel n n)
IsRefl_ZZ_Rel (a, b) = (multCommutative a b)

IsSym_ZZ_Rel : (n, m : ZZ1) -> (ZZ_Rel n m) -> (ZZ_Rel m n)
IsSym_ZZ_Rel (a, b) (c, d) pf_rel = (rewrite (multCommutative d a) in 
                                    (rewrite (multCommutative c b) in (sym pf_rel)))

congruence_1 : (ty1 : Type) -> (ty2 : Type) -> (a, b, c, d : ty1) -> 
               (f : ty1 -> ty1 -> ty2) -> (a = b) -> (c = d) -> ( (f a c) = (f b d) )
               
congruence_1 ty1 ty2 a a c c f Refl Refl = Refl

IsTrans_ZZ_Rel : (a, b, c : ZZ1) -> (ZZ_Rel a b) -> (ZZ_Rel b c) -> (ZZ_Rel a c)
IsTrans_ZZ_Rel (a, b) (c, d) (k, l) pf1 pf2 = let
    
    pf3 : (mult (mult a d) (mult c l) = mult (mult b c) (mult d k)) 
        = congruence_1 Nat Nat (mult a d) (mult b c) (mult c l) (mult d k) mult pf1 pf2
    
    pf4 : (mult a (mult d (mult c l)) = mult (mult a d) (mult c l)) 
        = multAssociative a d (mult c l)
        
    pf5 : (mult b (mult c (mult d k)) = mult (mult b c) (mult d k))
        = multAssociative b c (mult d k)    
        
    pf6 : (mult c l = mult l c)
        = multCommutative c l
        
    pf7 : (mult d (mult c l) = mult d (mult l c))
        = congruence Nat Nat (mult c l) (mult l c) (\x => (mult d x)) pf6
        
    pf8 : (mult d (mult l c) = mult (mult d l) c)
        = multAssociative d l c 
        
    pf9 : (mult d (mult c l) = mult (mult d l) c)
        = trans pf7 pf8
        
    pf10 : (mult d l = mult l d)
         = multCommutative d l
         
    pf11 : (mult (mult d l) c = mult (mult l d) c)
         = congruence Nat Nat (mult d l) (mult l d) (\x => (mult x c)) pf10                 
    
    pf12 : ( mult d (mult l c) = mult (mult l d) c )
         = trans pf8 pf11
         
    pf13 : (mult d (mult c l) = mult (mult l d) c)
         = trans pf7 pf12
    
    pf14 : (mult l (mult d c) = mult (mult l d) c)
         = multAssociative l d c          
         
    pf15 : ( mult (mult d l) c = mult l (mult d c) )
         = trans pf11 (sym pf14)
         
    pf16 : (mult d (mult c l) = mult l (mult d c))
         = trans pf9 pf15
         
    pf17 : (mult a (mult d (mult c l)) = mult a (mult l (mult d c)))
         = congruence Nat Nat (mult d (mult c l)) (mult l (mult d c)) (\x => (mult a x)) pf16               
    
    pf18 : (mult a (mult l (mult d c)) = mult (mult a l) (mult d c))
         = multAssociative a l (mult d c)
    
    pf19 : (mult (mult a d) (mult c l) = mult (mult a l) (mult d c))
         = trans (trans (sym pf4) pf17) pf18
            
    in
    ?rhs
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
