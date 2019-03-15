 module Lecture.GCD

switchLTE : (n: Nat) -> (m: Nat) -> (contra : (LTE n m) -> Void) -> LTE m n
switchLTE Z m contra = void (contra (LTEZero))
switchLTE (S k) Z contra = LTEZero
switchLTE (S k) (S j) contra =
  LTESucc (switchLTE k j previousContra) where
    previousContra = \evidence : (LTE k j) => contra (LTESucc evidence)

EuclidIndAux_rhs_2 : (x : LTE left right) -> Nat
EuclidIndAux_rhs_2 x = ?EuclidIndAux_rhs_2_rhs

gcdAux: (n: Nat) -> (m: Nat) -> (LTE m n) -> Nat
gcdAux n Z LTEZero = n
gcdAux (S right) (S left) (LTESucc x) = EuclidIndAux_rhs_2 x

gcd : Nat -> Nat -> Nat
gcd k j = case isLTE j k of
               (Yes prf) => gcdAux k j prf
               (No contra) => gcdAux j k (switchLTE j k contra)
