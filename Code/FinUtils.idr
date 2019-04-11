module FinUtils
import Data.Fin

%access public export

--Fin to Nat
tonatFin: (n: Nat) -> Fin(n) -> Nat
tonatFin (S k) FZ = Z
tonatFin (S k) (FS x) = S (tonatFin k x)

--Euclid's div
Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat)
Eucl Z b = (0,0)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False => (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True => (0, S k)
--Nat to Fin (NOT modular values; if it overflows, the result is 0)
tofinNat: (a: Nat) -> (n: Nat) -> Fin n
tofinNat a Z = assert_unreachable
tofinNat Z (S k) = FZ
tofinNat (S j) (S k) = case (lte (S j) (S k)) of
                             False => FS (tofinNat j k)
                             True => FZ

--adding two Fin n's
-- addfin: (n: Nat) -> Fin (S n) -> Fin (S n) -> Fin (S n) -> (Fin (S n), Fin (S n))
-- addfin n x y z = case (tofin ((tonatFin (S n) x)+ (tonatFin (S n) y) + (tonatFin (S n) z)) (S n)) of
--                     [l] => (FZ, l)
--                     [k, l] => (k,l)

-- embedding Fin n in Fin S n vertically
embn: (n: Nat) -> Fin n -> Fin (S n)
embn (S k) FZ = FZ
embn (S k) (FS x) = FS (embn k x)

--Unused mulfinNat - multiplies two Fin n's
-- mulfinNat: (n: Nat) -> Fin (n) -> Fin (n) -> (Fin (n), Fin (n))
-- mulfinNat (S n) x y =  case tofin ((tonatFin (S n) x)*(tonatFin (S n) y)) (S n) of
--                     [l] => (FZ, l)
--                     [k,l] => (k,l)
