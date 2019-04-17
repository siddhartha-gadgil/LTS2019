module ZZmult

import congruence
import Quotient_Type
import ZZ_alt
import Product_Type_Eq
import ZZplus

%access public export
%default total

mult : ZZ1 -> ZZ1 -> ZZ1
mult (a, b) (c, d) =
    ((plus (mult a c) (mult b d)), (plus (mult b c) (mult a d)))
