module LinearAlgebra

%access public export

import BaseN
import MultiSolver
import MatrixNumeric
import Data.Vect
import Data.Fin
import Matrix
import ZZ
import Rationals_2

-- Some auxillary functions for elementary operations

SimpleCast:  (v1:(Vect (k+ (S Z)) elem)) ->( Vect (S k) elem)  -- necessary for type matching
SimpleCast {k} v1 = (Vecttake (S k) v1)

RowN: Matrix n n ZZPair -> (k: Nat) -> Vect n ZZPair -- returns the nth row (indexing from 0)
RowN {n} x k = Data.Vect.index (tofinNat k n) x

ColumnN: Matrix n n ZZPair -> (k: Nat) -> Vect n ZZPair --returns the nth column (indexing from 0)
ColumnN {n} x k = Data.Vect.index (tofinNat k n) (transpose x)

VectorSubtract: (n: Nat) -> (a: Vect n ZZPair) -> (b: Vect n ZZPair) -> (Vect n ZZPair) --subtracts components
VectorSubtract n a b = a - b

ScaleVect: (n: Nat) -> (Vect n ZZPair) -> (c: ZZPair) -> (Vect n ZZPair) --scales by a rational
ScaleVect n xs c = c <# xs

--returns the row scaled by a constant minus another vector (used in row operations)

axpy: (n: Nat) -> (a: Vect n ZZPair) -> (b: Vect n ZZPair) -> (c: ZZPair) -> (Vect n ZZPair)
axpy n a b c = VectorSubtract (n) (a) (ScaleVect (n) b c)

--Auxillary functions, will be used in the Gauss-Jordan process

First_k_rows: (n: Nat) -> (x: Matrix n n ZZPair) -> (k: Nat) -> Matrix k n ZZPair
First_k_rows n x Z = []
First_k_rows n x (S k) = [RowN x k] ++ (First_k_rows n x k)

Last_k_rows: (n: Nat) -> (x: Matrix n n ZZPair) -> (k: Nat) -> Matrix k n ZZPair
Last_k_rows n x k = reverse (First_k_rows n (reverse x) k)

First_k_rows_from_RowP: (n: Nat) -> (x: Matrix n n ZZPair) -> (p: Nat) -> (k: Nat) -> Matrix k n ZZPair
First_k_rows_from_RowP n x p Z = []
First_k_rows_from_RowP n x p (S k) = SimpleCast ((First_k_rows_from_RowP n x p k) ++ [RowN x (p+k)])

-- A section on elementary operations (to eventually implement the Gauss-Jordan process)

-- Swaps two rows in a matrix (indexing from 0)

SwapRows: (n: Nat) -> Matrix n n ZZPair -> (a: Nat) -> (b: Nat) -> Matrix n n ZZPair
SwapRows n x a b = replaceAt (tofinNat b n) (RowN x a) (replaceAt (tofinNat a n) (RowN x b) (x))

-- Performs an elementary row operation, subtracts from ROW A the ROW B scaled by C (A -> A - C*B)

RowOperation: (n: Nat) -> Matrix n n ZZPair -> (a: Nat) -> (b: Nat) -> (c: ZZPair) -> Matrix n n ZZPair
RowOperation n x a b c = replaceAt (tofinNat a n) (axpy n (RowN x a) (RowN x b) c) (x)
