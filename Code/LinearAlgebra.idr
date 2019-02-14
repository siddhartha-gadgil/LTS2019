module LinearAlgebra

import BaseN
import MultiSolver
import Data.Matrix.Numeric
import Data.Vect
import Data.Fin
import Data.Matrix
import ZZ
import Rationals

%access public export

-- Some auxillary functions for elementary operations

--Takes the first m elements from a vector
Vecttake : (m:Nat)->Vect n elem->Vect m  elem
Vecttake Z xs = []
Vecttake (S k) (x::xs) = x::(Vecttake k xs)

FST: ZZPair -> ZZ --some issue with fst
FST (a, b) = a

Pred: Nat -> Nat -- needed to get (n-1) for number of operations
Pred Z = Z
Pred (S k) = k

SimpleCast:  (v1:(Vect (k+ (S Z)) elem)) ->( Vect (S k) elem)  -- necessary for type matching, taken from Shafil's code
SimpleCast {k} v1 = (Vecttake (S k) v1)

RowN: Matrix n n ZZPair -> (k: Nat) -> Vect n ZZPair -- returns the nth row (indexing from 0)
RowN {n} x k = Data.Vect.index (tofinNat k n) x

ij: Matrix n n ZZPair -> (i: Nat) -> (j: Nat) -> ZZPair
ij {n} x i j = Data.Vect.index (tofinNat j n) (RowN x i)

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

-- Scales a row by dividing it by a rational number.

ScaleRow: (n: Nat) -> Matrix n n ZZPair -> (row_a: Nat) -> (c: ZZPair) -> Matrix n n ZZPair
ScaleRow n x row_a c = replaceAt (tofinNat row_a n) (ScaleVect n (RowN x row_a) c) (x)

-- Swaps two rows in a matrix (indexing from 0)

SwapRows: (n: Nat) -> Matrix n n ZZPair -> (a: Nat) -> (b: Nat) -> Matrix n n ZZPair
SwapRows n x a b = replaceAt (tofinNat b n) (RowN x a) (replaceAt (tofinNat a n) (RowN x b) (x))

-- Performs an elementary row operation, subtracts from row a the row b scaled by c

RowOperation: (n: Nat) -> Matrix n n ZZPair -> (a: Nat) -> (b: Nat) -> (c: ZZPair) -> Matrix n n ZZPair
RowOperation n x a b c = replaceAt (tofinNat a n) (axpy n (RowN x a) (RowN x b) c) (x)

-- Makes the kth number in Row A zero by subtracting a scaling of Row B (for upper triangularizing)
-- As usual, indexing starts from 0

MakeElementZero: (n: Nat) -> (x: Matrix n n ZZPair) -> (row_a : Nat) -> (row_b : Nat) -> (pos : Nat) -> Matrix n n ZZPair
MakeElementZero n x row_a row_b pos = case (FST(ij x row_a pos)) of
                                      (Pos Z) => x
                                      (Pos (S k)) => case ((fst (ij x row_b pos))) of
                                                                          (Pos Z) => (SwapRows n x row_a row_b)
                                                                          (Pos (S k)) => (RowOperation n x row_a row_b (divZZ (ij x row_a pos) (ij x row_b pos)) )
                                                                          (NegS k) => (RowOperation n x row_a row_b (divZZ (ij x row_a pos) (ij x row_b pos)) )
                                      (NegS k) => case ((fst (ij x row_b pos))) of
                                                                          (Pos Z) => (SwapRows n x row_a row_b)
                                                                          (Pos (S k)) => (RowOperation n x row_a row_b (divZZ (ij x row_a pos) (ij x row_b pos)) )
                                                                          (NegS k) => (RowOperation n x row_a row_b (divZZ (ij x row_a pos) (ij x row_b pos)) )

-- Explanation: We want to transform the element x[row_a][pos] into zero by a row operation. There are a few different cases
--              1. If x[row_a][pos] is already zero, nothing needs to be done.
--              2. If not, we scale row_b appropriately and do a row operation (A -> A - cB)
--              3. If x[row_b][pos] is zero, however, no row operation will work. We simply swap the
--                 row_a and row_b here; then, x[row_a][pos] will become zero.

-- This algorithm is important to make a matrix upper-triangular.

MakeColumnZero: (n: Nat) -> (x: Matrix n n ZZPair) -> (col : Nat) -> (iter : Nat) -> Matrix n n ZZPair
MakeColumnZero n x col Z = x
MakeColumnZero n x col (S k) = case (isLTE (S k) col) of
                                   (Yes prf) => x
                                   (No contra) => (MakeColumnZero n (MakeElementZero n x (S k) col col) col k)

-- This function turns a column into what it should be in upper-triangular form by adding in the necessary zeros.
-- iter is a variable to induct on (trick courtesy Sriram)
-- When using this, make sure to set "iter" as n-1 (1 less than the number of rows)

-- The next step here is to use the above function to make a matrix upper triangular. This can be
-- done by inducting on the number of columns.

-- A helper function, which recursively fills zeros into columns.

UpperTriangularize: (x: Matrix n n ZZPair) -> (iter: Nat) -> Matrix n n ZZPair
UpperTriangularize {n} x Z = (MakeColumnZero n x Z (Pred n)) -- Column Zero is the base case
UpperTriangularize {n} x (S k) = (MakeColumnZero n (UpperTriangularize x k) (S k) (Pred n))

-- Enter a matrix, get the upper triangular form.

UpperTriangularForm: (x: Matrix n n ZZPair) -> Matrix n n ZZPair
UpperTriangularForm {n} x = UpperTriangularize x (Pred (Pred n))

-- The function below converts a matrix into a Diagonal Form (note that this is NOT diagonalization!) by converting to upper-triangular
-- form, transposing that (to get a lower triangular matrix) and finding the upper-triangular form of the tranpose. This is going to be useful
-- as it is the next step of the Gauss-Jordan algorithm (what's next: divide out the rows to get an identity matrix; an inverse can be
-- found this way by applying all the above row operations to an identity matrix.

DiagonalForm: (x: Matrix n n ZZPair) -> Matrix n n ZZPair
DiagonalForm {n} x = UpperTriangularForm (transpose (UpperTriangularForm x))

-- once a matrix is in diagonal form, we can convert it to the identity by dividing each row by its only nonzero element

ReduceRow: (x: Matrix n n ZZPair) -> (iter: Nat) -> Matrix n n ZZPair
ReduceRow {n = n} x Z = ScaleRow n x Z (divZZ (1,1) (ij x 0 0))
ReduceRow {n = n} x (S k) = ScaleRow n (ReduceRow x k) (S k) (divZZ (1,1) (ij x (S k) (S k)))

-- This function converts any matrix into the identity. Applying the row operations which do this to an identity matrix would convert it
-- to an inverse. If we want to solve linear equations, this would be enough (for proof, we would need to prove that AA^-1 = I). 
-- Another possibility would be to use back-substitution from the upper-triangular form. This would be simpler because the function
-- GeneralEqSolver from Linear.idr could be modified a bit to solve n successive 1 - variable equations, and generating a proof would
-- be easier.

MakeIdentity: (x: Matrix n n ZZPair) -> (Matrix n n ZZPair)
MakeIdentity {n} x = ReduceRow (DiagonalForm x) (Pred n)

-- Once we have a matrix in diagonal (or even upper triangular) form, we can calculate the magnitude of its determinant by multiplying
-- the diagonal elements.

DiagonalProductHelper: (x: Matrix n n ZZPair) -> (iter: Nat) -> ZZPair
DiagonalProductHelper x Z = (ij x 0 0)
DiagonalProductHelper x (S k) = (ij x (S k) (S k)) * (DiagonalProductHelper x k)

-- Calculates the determinant up to the sign ( (-1)^n to be implemented later ). Effectively, this calculates the "volume" of n-vectors in
-- n-dimensional Euclidean space. 

DetUpToSign: (x: Matrix n n ZZPair) -> ZZPair
DetUpToSign {n} x = simplifyRational (DiagonalProductHelper (DiagonalForm x) (Pred n))

-- I propose a simple way to calculate the sign factor: in the conversion to upper-triangular form, the last column is untouched
-- except for by Row Swapping. The last column in upper - triangular form is thus a permutation of the last column of the original 
-- matrix. We just need to check if this is an odd or even permutation (simplification of all elements of the matrices will be 
-- necessary to ensure that this can be carried out) and multiply appropriately.



