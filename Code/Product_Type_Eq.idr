module Product_Type_Eq

%access public export
%default total

||| A proof that equality for product types are generate by the equalities of the componenets

Product_Eq_property_1 : (ty1, ty2 : Type) -> (a, b : (ty1, ty2)) ->
                        ( (fst a) = (fst b) ) -> ( (snd a) = (snd b) ) ->
                        ( a = b )

Product_Eq_property_1 ty1 ty2 (x, y) (x, y) Refl Refl = Refl







