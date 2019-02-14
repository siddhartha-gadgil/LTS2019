module Basen

import Data.Fin

%access public export
--Fin to Nat
tonatFin: (n: Nat) -> Fin(n) -> Nat
tonatFin (S k) FZ = Z
tonatFin (S k) (FS x) = S (tonatFin k x)

--List Fin to Nat
tonat: (n: Nat) -> List (Fin(n)) -> Nat
tonat n [] = Z
tonat n (x :: xs) = (tonatFin n x)*(power n (length xs)) + (tonat n xs)


--Euclid's div
Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat)
Eucl Z b = (0,0)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False => (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True => (0, S k)

--Nat to Fin (modular values)
tofinNat: (a: Nat) -> (n: Nat) -> Fin n
tofinNat Z (S j) = FZ
tofinNat (S k) (S j) = case lte (S k) (S j) of
                True => FS (tofinNat k j)
                False =>  (tofinNat (snd(Eucl (S k) (S j))) (S j))

--left strips FZ from lists
strp: List (Fin n) -> List (Fin n)
strp [] = []
strp (x :: xs) = case x of
                      FZ => strp(xs)
                      (FS y) => x::xs

-- Nat to List Fin n (base n representation)
tofin: Nat -> (n: Nat) -> List (Fin n)
tofin Z (S j) = [FZ]
tofin (S k) (S j) = strp(reverse(rem :: reverse(tofin q (S j)))) where
                    rem = tofinNat (snd(Eucl (S k) (S j))) (S j)
                    q = fst(Eucl (S k) (S j))
                    
--embedding Fin n in Fin S n vertically
embn: (n: Nat) -> Fin n -> Fin (S n)
embn (S k) FZ = FZ
embn (S k) (FS x) = FS (embn k x)

--Generates n in (Fin (S n))
Genn: (n: Nat) -> (Fin (S n))
Genn Z = FZ
Genn (S k) = FS (Genn k)

--Checks if a given element of Fin (S n) is in fact n
Isn: (n: Nat) -> (Fin (S n)) -> Bool
Isn Z x = True
Isn (S k) FZ = False
Isn (S k) (FS x) = Isn k x

--Proves that the definitional equality for Isn holds
IsnisIsn: (n: Nat) -> (p: Fin (S n)) -> (Isn (S n) (FS p)) = (Isn n p)
IsnisIsn n p = Refl

--Proves that if a given (FS x) is not n in (Fin (S n)), then x is not n-1 in (Fin n)
IsNotnPf:  (n: Nat) -> (p: Fin (S n)) ->  ((Isn (S n) (FS p)) = False) -> ((Isn n p) = False)
IsNotnPf Z _ Refl impossible
IsNotnPf (S k) FZ prf = Refl
IsNotnPf (S k) (FS x) prf = trans (sym (IsnisIsn (S k) (FS x))) prf

--Gives a back embedding whenever the value is not Genn
Predec: (n: Nat) -> (p: Fin (S n)) -> ((Isn n p) = False) -> (Fin n)
Predec Z _ Refl impossible
Predec (S k) FZ Refl = FZ
Predec (S k) (FS x) prf = FS (Predec k x (IsNotnPf (S k) (FS x) prf))

--A type in some sense resembling the decidable type for truth of Isn (with contra replaced by equality to False)
DecIsn: (n: Nat) -> (p: (Fin (S n))) -> Either (Isn n p = True) (Isn n p = False)
DecIsn Z p = Left Refl
DecIsn (S k) FZ = Right Refl
DecIsn (S k) (FS x) = case (DecIsn k x) of
                        Left l => Left (trans (IsnisIsn k x) l)
                        Right r => Right (trans (IsnisIsn k x) r)

--adding two Fin n's
addfin: (n: Nat) -> Fin (S n) -> Fin (S n) -> (Fin (S n), Fin (S n))
addfin Z x y = (FZ,  FZ)
addfin (S k) FZ y = (FZ, y)
addfin (S k) (FS x) y = let
                    a = Genn (S k)
                    b = the (Fin (S (S k))) FZ
                    c = the (Fin (S k)) FZ
                    w = fst(addfin (S k) (embn (S k) x) y)
                    z = snd(addfin (S k) (embn (S k) x) y)
                    in
                    case (DecIsn (S k) z) of
                             Left l => (FS c, b)
                             Right r => (w, FS(Predec (S k) z r))

--adding two reversed lists as specified
addfinl: (n: Nat) -> List (Fin (S n)) -> List (Fin (S n)) -> List (Fin (S n))
addfinl n [] ys = strp(ys)
addfinl n (x :: xs) [] = strp(x::xs)
addfinl n (x :: xs) (y :: ys) = (snd(addfin n FZ x y)::(addfinl n (addfinl n [fst(addfin n FZ x y)] xs) ys))

--adding two lists
addfinlist: (n: Nat) -> List (Fin (S n)) -> List (Fin (S n)) -> List (Fin (S n))
addfinlist n xs ys = reverse(addfinl n (reverse xs) (reverse ys))


--Unused mulfinNat - multiplies two Fin n's
mulfinNat: (n: Nat) -> Fin (n) -> Fin (n) -> (Fin (n), Fin (n))
mulfinNat (S n) x y =  case tofin ((tonatFin (S n) x)*(tonatFin (S n) y)) (S n) of
                    [l] => (FZ, l)
                    [k,l] => (k,l)

--multiply two reversed lists in Fin S n
mulfinl: (n: Nat) -> List (Fin (S n)) -> List (Fin (S n)) -> List (Fin (S n))
mulfinl n xs [] = []
mulfinl n xs (FZ :: ys) = FZ :: (mulfinl n xs ys)
mulfinl n xs ((FS x) :: ys) = addfinl n (mulfinl n xs ((embn n x)::ys)) xs

--multpily two lists
mulfinList: (n: Nat) -> List (Fin (S n)) -> List (Fin (S n)) -> List (Fin (S n))
mulfinList n xs ys = reverse(mulfinl n (reverse xs) (reverse ys))

--proof that right addition preserves equality (somehow cong was messing up)
addl: (x: Type) -> (z: List x) -> (l = y) -> (l ++ z = y ++ z)
addl x z Refl = Refl

-- Proof that the auxiliary reverseOnto used to define rev behaves the way it should (semi-pseudo-contravariantly as I choose to call it)
revontoeq: (x: Type) -> (y: List x) -> (l: List x) -> ((reverseOnto y l)  = ((reverseOnto [] l) ++ y))
revontoeq x y [] = Refl
revontoeq x [] (z :: xs) = sym (appendNilRightNeutral (reverseOnto [] (z::xs)))
revontoeq x (y :: ys) (z :: xs) = trans (trans (revontoeq x (z::y::ys) xs) ((appendAssociative (reverseOnto [] xs) [z] (y::ys)))) (sym (addl x (y::ys) (revontoeq x [z] xs)))

--Proof that reverse is pseudo-contravariant on concatenation
reviscontra: (x: Type) -> (y: List x) -> (l: List x) -> (reverse(y++l) =  reverse(l)++reverse(y))
reviscontra x [] z = sym (appendNilRightNeutral (reverseOnto [] z))
reviscontra x (y :: xs) z = trans (trans (trans (revontoeq x [y] (xs++z)) (addl x [y] (reviscontra x xs z))) (sym (appendAssociative (reverse z) (reverse xs) [y]))) (cong(sym (revontoeq x [y] xs)))

-- Proof that the reverse function is self-inverse
reveq: (x: Type) -> (l: List x) -> (l = reverse(reverse l))
reveq x [] = Refl
reveq x (y :: xs) = sym (trans (trans (cong(reviscontra x [y] xs)) (reviscontra x (reverse xs) (reverse [y]))) (cong(sym (reveq x xs))))

--Proof that any number of leading zeroes leave the natural number unchanged
pffinstrp: (n: Nat) -> (l: List(Fin (S n))) -> ((tonat (S n) (strp l)) = (tonat (S n) l))
pffinstrp n [] = Refl
pffinstrp n (x :: xs) = case x of
                              FZ => pffinstrp n xs
                              FS x => Refl

--Proof that the revrse of the empty list is itself
revnull: (reverse [] = [])
revnull = Refl

--Custom "functions are functors" function
ap: (x: Type) -> (y: Type) -> (f: x->y) -> (n = m) -> (f n = f m)
ap x y f Refl = Refl

{-
Proofs that don't work


addfinlZ: addfinl Z [] [] = []
addfinlZ = Refl


addfinlnullnull: (n: Nat) -> (y: List (Fin (S n))) -> addfinl n [] y = y
addfinlnullnull n y = Refl

addfinlnull: (n: Nat) -> (x: List (Fin (S n))) -> ((addfinl n (reverse x) (reverse [])) = reverse x)
addfinlnull n [] = ?l1 -- (ap (List (Fin (S n))) (List (Fin (S n))) (\y => addfinl n y y) revnull)
addfinlnull n (x :: xs) = ?l_2

fintonatadd: (n: Nat) -> (m: List (Fin (S n))) -> (l: List (Fin (S n))) -> ((tonat (S n) (addfinlist n m l)) = (tonat (S n) m) + (tonat (S n) l))
fintonatadd n m [] = ?lp --trans (sym (trans (trans (sym (pffinstrp n m)) (cong (reveq (Fin (S n)) m))) (cong {f = (\x => ( tonat (S n)(strp (reverse x))))} Refl))) (sym (plusZeroRightNeutral (tonat (S n) m)))
fintonatadd n m (x :: xs) = ?l
-}

