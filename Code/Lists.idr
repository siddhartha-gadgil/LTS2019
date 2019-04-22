module Lists

%access public export
%default total


--proof that something is an element of the list
total
isElementOfList : (typ : Type) -> (ls : List typ) -> (a : typ) -> Type
isElementOfList typ ls a = (n : Nat ** (fromMaybe (index' n ls) = a))

--proof that right addition preserves equality (somehow cong was messing up)
total
addl: (x: Type) -> (z: List x) -> (l = y) -> (l ++ z = y ++ z)
addl x z Refl = Refl

-- Proof that the auxiliary reverseOnto used to define rev behaves the way it should (semi-pseudo-contravariantly as I choose to call it)
total
revontoeq: (x: Type) -> (y: List x) -> (l: List x) -> ((reverseOnto y l)  = ((reverseOnto [] l) ++ y))
revontoeq x y [] = Refl
revontoeq x [] (z :: xs) = sym (appendNilRightNeutral (reverseOnto [] (z::xs)))
revontoeq x (y :: ys) (z :: xs) = trans (trans (revontoeq x (z::y::ys) xs) ((appendAssociative (reverseOnto [] xs) [z] (y::ys)))) (sym (addl x (y::ys) (revontoeq x [z] xs)))

--Proof that reverse is pseudo-contravariant on concatenation
total
reviscontra: (x: Type) -> (y: List x) -> (l: List x) -> (reverse(y++l) =  reverse(l)++reverse(y))
reviscontra x [] z = sym (appendNilRightNeutral (reverseOnto [] z))
reviscontra x (y :: xs) z = trans (trans (trans (revontoeq x [y] (xs++z)) (addl x [y] (reviscontra x xs z))) (sym (appendAssociative (reverse z) (reverse xs) [y]))) (cong(sym (revontoeq x [y] xs)))

-- Proof that the reverse function is self-inverse
total
reveq: (x: Type) -> (l: List x) -> (l = reverse(reverse l))
reveq x [] = Refl
reveq x (y :: xs) = sym (trans (trans (cong(reviscontra x [y] xs)) (reviscontra x (reverse xs) (reverse [y]))) (cong(sym (reveq x xs))))
