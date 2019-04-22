module LTE_Properties

-- properties of LTE

%access public export
%default total

LTE_Property1 : (a : Nat) -> (LTE a a)
LTE_Property1 Z = LTEZero
LTE_Property1 (S k) = LTESucc (LTE_Property1 k)

LTE_Property2 : (a, x, y : Nat) -> (LTE a x) -> (LTE x y) -> (LTE a y)
LTE_Property2 Z x y pf1 pf2 = LTEZero
LTE_Property2 (S k) (S l) (S m) (LTESucc pf1) (LTESucc pf2) = 
    LTESucc (LTE_Property2 k l m pf1 pf2)
