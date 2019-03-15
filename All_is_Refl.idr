-- trying to prove that everything is equal to Refl

total
all_is_Refl : (typ : Type) -> (a : typ) -> (p : (a = a)) -> (p = Refl)
all_is_Refl typ a Refl = Refl
