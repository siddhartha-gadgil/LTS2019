module BaseN

import Data.Fin
import ZZ
import GCDZZ
import gcd
import ZZUtils
import NatUtils
import NatOrder

%access public export

--Defines a data type Base that behaves like a list
data Base: (n: Nat) -> Type where
  Ones: (n: Nat) -> (Fin n) -> Base n
  Next: (n: Nat) -> (Fin n) -> (Base n) -> (Base n)

--Auxiliary function that reverses a Base (S n) onto anpther given Base (S n)
total
Revonto: (n: Nat) -> (Base (S n)) -> (Base (S n)) -> (Base (S n))
Revonto n accum (Ones (S n) x) = Next (S n) x accum
Revonto n accum (Next (S n) x y) = Revonto n (Next (S n) x accum) y

--Reverses a Base (S n)
total
Rev: (n: Nat) -> (Base (S n)) -> (Base (S n))
Rev n (Ones (S n) x) = Ones (S n) x
Rev n (Next (S n) x y) = Revonto n (Ones (S n) x) y

--Concatenates two values in Base (S n)
total
concat: (n: Nat) -> (Base (S n)) -> (Base (S n)) -> (Base (S n))
concat n (Ones (S n) x) y = Next (S n) x y
concat n (Next (S n) x z) y = Next (S n) x (concat n z y)

--Fin to Nat
total
tonatFin: (n: Nat) -> Fin(S n) -> Nat
tonatFin Z FZ = Z
tonatFin (S k) FZ = Z
tonatFin (S k) (FS x) = S (tonatFin k x)

--Outputs the length of a number in base n
total
len: (n: Nat) -> Base (S n) -> Nat
len n (Ones (S n) x) = S Z
len n (Next (S n) x y) = S(len n y)

--List Fin to Nat
total
tonat: (n: Nat) -> Base (S n) -> Nat
tonat Z y = case y of
            (Ones (S Z) x) => case x of
                              FZ => Z
                              FS x impossible
            (Next (S Z) x z) => case x of
                              FZ => Z
                              FS x impossible
tonat (S k) y = case y of
            (Ones (S (S k)) x) => case x of
                                  FZ => Z
                                  FS x => S(tonat k (Ones (S k) x))
            (Next (S (S k)) x z) => case x of
                                    FZ => tonat (S k) z
                                    FS w => (S(tonat k (Ones (S k) w)))*(pow (S (S k)) (len (S k) z)) + (tonat (S k) z)

total
tonatFindef: tonatFin (S Z) FZ = Z
tonatFindef = Refl

total
tonatdef: tonat Z (Ones (S Z) FZ) = Z
tonatdef = Refl

--Nat to Fin (modular values)
total
tofinNath: (a: Nat) -> (n: Nat) -> (k: Nat) -> Fin (S n)
tofinNath r Z k = FZ
tofinNath r (S j) Z = FZ
tofinNath Z (S j) (S r) = FZ
tofinNath (S k) (S j) (S r) = f k j r (lte (S k) (S j)) where
          f: (k: Nat) -> (j: Nat) -> (r: Nat) -> (t: Bool) -> Fin (S (S j))
          f k j r True = FS (tofinNath k j r)
          f k j r False = let qrem = eculidDivideAux (S k) (S j) (SIsNotZ) in
                (tofinNath (DPair.fst(DPair.snd(qrem))) (S j) r)


total
tofinNat: (a: Nat) -> (n: Nat) -> Fin (S n)
tofinNat a n = tofinNath a n (n+2)

total
tonatfinlte: (n: Nat) -> (a: Fin (S n)) -> (lte (tonatFin n a) n) = True
tonatfinlte Z FZ = Refl
tonatfinlte Z (FS x) impossible
tonatfinlte (S k) FZ = Refl
tonatfinlte (S k) (FS x) = (tonatfinlte k x)

total
FinNatop: (n: Nat) -> (a: Fin (S n)) -> (tofinNat (tonatFin n a) n) = a
FinNatop Z FZ = Refl
FinNatop Z (FS x) impossible
FinNatop (S k) FZ = Refl
FinNatop (S k) (FS x) = trans (cong(tonatfinlte (S k) (FS x))) (cong(FinNatop k x))

total
Remn: (a: Nat) -> (n: Nat) -> (r: Nat ** (lte r (S n) = True))
Remn a n = let
            qrem = eculidDivideAux a (S n) (SIsNotZ)
            rem = DPair.fst(DPair.snd(qrem))
            in
            MkDPair rem (LTEmeanslteTrue rem (S n) (ltImpliesLTE (Basics.snd(DPair.snd(DPair.snd(qrem))))))

total
strp: (Base (S n)) -> (Base (S n))
strp (Ones (S n) x) = (Ones (S n) x)
strp (Next (S n) x y) = case x of
                  FZ => strp(y)
                  FS z => Next (S n) x y

-- Nat to List Fin n (base n representation)
total
tofinh: Nat -> (n: Nat) -> (r: Nat) -> Base (S n)
tofinh Z n r = Ones (S n) FZ
tofinh k n Z = Ones (S n) FZ
tofinh (S k) n (S r) = strp(concat n (tofinh q n r) (Ones (S n) rem)) where
                    qrem: (q : Nat ** (r : Nat ** (((S k) = r + (q * (S n))), LT r (S n))))
                    qrem = eculidDivideAux (S k) (S n) (SIsNotZ)
                    rem: Fin (S n)
                    rem = tofinNat (DPair.fst(DPair.snd(qrem))) n
                    q: Nat
                    q = DPair.fst(qrem)

total
tofin: Nat -> (n: Nat) -> Base (S n)
tofin k n = tofinh k n k

--embedding Fin n in Fin S n vertically
total
embn: (n: Nat) -> Fin n -> Fin (S n)
embn (S k) FZ = FZ
embn (S k) (FS x) = FS (embn k x)

--Generates n in (Fin (S n))
total
Genn: (n: Nat) -> (Fin (S n))
Genn Z = FZ
Genn (S k) = FS (Genn k)

--Checks if a given element of Fin (S n) is in fact n
total
Isn: (n: Nat) -> (p: Fin (S n)) -> Bool
Isn Z x = True
Isn (S k) FZ = False
Isn (S k) (FS x) = Isn k x

--Proves that the definitional equality for Isn holds
total
IsnisIsn: (n: Nat) -> (p: Fin (S n)) -> (Isn (S n) (FS p)) = (Isn n p)
IsnisIsn n p = Refl

--Proves that if a given (FS x) is not n in (Fin (S n)), then x is not n-1 in (Fin n)
total
IsNotnPf:  (n: Nat) -> (p: Fin (S n)) ->  ((Isn (S n) (FS p)) = False) -> ((Isn n p) = False)
IsNotnPf Z _ Refl impossible
IsNotnPf (S k) FZ prf = Refl
IsNotnPf (S k) (FS x) prf = trans (sym (IsnisIsn (S k) (FS x))) prf

--Gives a back embedding whenever the value is not Genn
total
Predec: (n: Nat) -> (p: Fin (S n)) -> ((Isn n p) = False) -> (Fin n)
Predec Z _ Refl impossible
Predec (S k) FZ Refl = FZ
Predec (S k) (FS x) prf = FS (Predec k x (IsNotnPf (S k) (FS x) prf))

--Decidable type for Isn
total
DecIsn: (n: Nat) -> (p: (Fin (S n))) -> Either (Isn n p = True) (Isn n p = False)
DecIsn Z p = Left Refl
DecIsn (S k) FZ = Right Refl
DecIsn (S k) (FS x) = case (DecIsn k x) of
                        Left l => Left (trans (IsnisIsn k x) l)
                        Right r => Right (trans (IsnisIsn k x) r)

--adding two Fin n's
total
addfinh: (n: Nat) -> (k: Nat) -> Fin (S n) -> Fin (S n) -> (Fin (S n), Fin (S n))
addfinh k Z x y = (FZ, FZ)
addfinh Z (S r) x y = (FZ, FZ)
addfinh (S k) (S r) FZ y = (FZ, y)
addfinh (S k) (S r) (FS x) y = let
                    a = Genn (S k)
                    b = the (Fin (S (S k))) FZ
                    c = the (Fin (S k)) FZ
                    w = fst(addfinh (S k) r (embn (S k) x) y)
                    z = snd(addfinh (S k) r (embn (S k) x) y)
                    in
                    case (DecIsn (S k) z) of
                             Left l => (FS c, b)
                             Right r => (w, FS(Predec (S k) z r))

total
addfin: (n: Nat) -> Fin (S n) -> Fin (S n) -> (Fin (S n), Fin (S n))
addfin n x y = addfinh n (n+1) x y

--adding two reversed lists as specified
total
addfinlh: (n: Nat) -> (k: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
addfinlh n Z a b = (Ones (S n) FZ)
addfinlh n (S k) (Ones (S n) x) (Ones (S n) y) = case (addfin n x y) of
                              (FZ, a) => Ones (S n) a
                              (FS c, a) => Next (S n) a (Ones (S n) (FS c))
addfinlh n (S k) (Ones (S n) x) (Next (S n) y z) = Next (S n) (snd (addfin n x y)) (addfinlh n k (Ones (S n) (fst (addfin n x y))) z)
addfinlh n (S k) (Next (S n) x z) (Ones (S n) y) = Next (S n) (snd (addfin n x y)) (addfinlh n k (Ones (S n) (fst (addfin n x y))) z)
addfinlh n (S k) (Next (S n) x z) (Next (S n) y w) = Next (S n) (snd (addfin n x y)) (addfinlh n k (Ones (S n) (fst (addfin n x y))) (addfinlh n k z w))

total
addfinl: (n: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
addfinl n x y = addfinlh n (4*((len n x)+(len n y))) x y

--adding two lists
total
addfinlist: (n: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
addfinlist n xs ys = (Rev n (addfinl n (Rev n xs) (Rev n ys)))

--multiply two reversed lists in Fin S n
total
mulfinlh: (n: Nat) -> (k: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
mulfinlh n Z a b = Ones (S n) FZ
mulfinlh n (S k) (Ones (S n) FZ) y = Ones (S n) FZ
mulfinlh n (S k) (Ones (S n) (FS x)) y = addfinl n y (mulfinlh n k (Ones (S n) (embn n x)) y)
mulfinlh n (S k) (Next (S n) FZ z) y = Next (S n) FZ (mulfinlh n k z y)
mulfinlh n (S k) (Next (S n) (FS x) z) y = addfinl n y (mulfinlh n k (Next (S n) (embn n x) z) y)

total
mulfinl: (n: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
mulfinl n x y = mulfinlh n (tonat n x) x y

--multiply two lists
total
mulfinList: (n: Nat) -> (Base (S n)) -> (Base (S n)) -> (Base (S n))
mulfinList n xs ys = Rev n (mulfinl n (Rev n xs) (Rev n ys))

--Custom "functions are functors" function
total
ap: (x: Type) -> (y: Type) -> (f: x->y) -> (n = m) -> (f n = f m)
ap x y f Refl = Refl
