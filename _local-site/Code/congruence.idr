module congruences

||| Congruence
public export
congruence : (ty1, ty2 : Type) -> (a : ty1) -> (b : ty1) -> (f : ty1 -> ty2) -> (a = b) -> ((f a) = (f b))
congruence ty1 ty2 a a f Refl = Refl
