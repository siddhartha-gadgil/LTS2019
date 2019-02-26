module MultiSolver

--To make sure that all imports work, load in idris as
--   idris Linear.MultiSolver.idr -p contrib

import ZZ
import Data.Matrix.Numeric
import Data.Fin
import FinUtils
import Rationals

%access public export

{-
Representing a system of linear equations in matrix form as AX = B,
the solution for X is X = A^(-1)B
Unique solutions exist if |A| != 0.
If |A| == 0, the system can be either inconsistent (no sol.),
             or dependent (infinite sol.)
To Be Done:
- existence of solutions (depends on determinant)
- multiplication of matrices (Num interface defined)
- proof that solutions are correct
- etc.
-}

--Operations for (ZZ,ZZ) are defined, so that we can develop proofs
total
plusZZ : ZZPair -> ZZPair -> ZZPair
plusZZ x y = ((fst x)*(snd y) + (snd x)*(fst y), (snd x)*(snd y))

total
multZZ : ZZPair -> ZZPair -> ZZPair
multZZ x y = ((fst x)*(fst y), (snd x)*(snd y))

total
divZZ : ZZPair -> ZZPair -> ZZPair
divZZ x y = ((fst x)*(snd y), (snd x)*(fst y))

total
fromIntQ : Integer -> ZZPair
fromIntQ n = if n < 0
  then (NegS $ fromInteger ((-n) - 1), Pos 1)
  else (Pos $ fromInteger n, Pos 1)

--This allows arithmetic operations on ZZPair
implementation Num ZZPair where
  (+) = plusZZ
  (*) = multZZ
  fromInteger = fromIntQ

mutual
  implementation Neg ZZPair where
    negate (Pos Z, x)     = (Pos Z, x)
    negate (Pos (S n), x) = (NegS n, x)
    negate (NegS n, x)    = (Pos (S n), x)

    (-) = subZZ

  subZZ : ZZPair -> ZZPair -> ZZPair
  subZZ x y = plusZZ x (negate y)

--This can be used to check equality
(==) : ZZPair -> ZZPair -> Bool
(==) (a,b) (c,d) = (a*d) == (b*c)


--Minor for a term of a 1x1 Matrix (Not required, can be removed later)
total
minor1 : Fin 1 -> Fin 1 -> Matrix 1 1 ZZPair -> ZZPair
minor1 x y [[k]] = k

--Minor for a term of a 2x2 Matrix
total
minor2 : Fin 2 -> Fin 2 -> Matrix 2 2 ZZPair -> ZZPair
minor2 x y mat = indices 0 0 (subMatrix x y mat)

--Minor for a general matrix term (Indices are elements of Fin <size>)
minor : Fin (S n) -> Fin (S n) ->
  Matrix (S n) (S n) ZZPair -> ZZPair
minor {n} x y mat = case n of
                  Z => minor1 x y mat
                  (S Z) => minor2 x y mat
                  (S (S k)) => simplifyRational (det (subMatrix x y mat))

--Cofactor terms for a matrix (defined using the minor)
cofactor : Fin (S n) -> Fin (S n) ->
  Matrix (S n) (S n) ZZPair -> ZZPair
cofactor x y mat = case (modNatNZ (finToNat x + finToNat y) (S (S Z)) SIsNotZ) of
                        Z => minor x y mat
                        (S k) => (NegS 0, Pos 1) * (minor x y mat)

--To make calc simpler, I have defined the cofactor/determinant term, as
--this will be required for defining the inverse of a matrix
cofByDet : Fin (S n) -> Fin (S n) ->
  Matrix (S n) (S n) ZZPair -> ZZPair
cofByDet {n} x y mat = case n of
              Z => (snd (cofactor 0 0 mat), fst (cofactor 0 0 mat))
              (S k) => simplifyRational
                ((cofactor x y mat) * (snd (det mat), fst (det mat)))

--Auxillary functions for defining an empty matrix, which will be updated
--with values of the inverse

--Given n, give a vector of length n, with each element (0,1)
total
empRow : (n : Nat) -> Vect n ZZPair
empRow Z = []
empRow (S k) = [(Pos Z, Pos 1)] ++ (empRow k)

--Given m,n, give an empty mxn matrix with (0,1) filled for every term.
--This is the null matrix (in rationals, we defined 0 as (0,1))
total
empMat : (m : Nat) -> (n : Nat) -> Vect m (Vect n ZZPair)
empMat Z n = []
empMat (S k) n = [(empRow n)] ++ (empMat k n)

--Defining the cofactor matrix requires updating the null matrix
--with values of the cofactor.
--This requires inducting twice on the row and column, hence has
--been broken down into two separate functions.

--Given the reqRow, gives the row of cofactors for the original matrix
--for that index.
--iter is a variable used to induct on, and does not serve any
--real purpose
--"replaceAt index elem Vect" replaces an element of Vect at index by elem
--embn is from BaseN, and embeds an element of Fin n in Fin (S n)
cofRow : (size : Nat) -> (reqRow : Fin size) -> Matrix size size ZZPair ->
  (iter : Fin size) -> Vect size ZZPair
cofRow Z _ _ FZ impossible
cofRow Z _ _ (FS _) impossible

cofRow (S k) reqRow mat FZ =
                    replaceAt
                    0
                    (cofByDet reqRow 0 mat)
                    (empRow (S k))

cofRow (S k) reqRow mat (FS y) =
                    replaceAt
                    (FS y)
                    (cofByDet reqRow (FS y) mat)
                    (cofRow (S k) reqRow mat (embn k y))

--Now, we can construct the cofactor matrix from the formed cofactor rows.
--tofinNat is from BaseN, and converts an element of Nat to Fin.
cofMat : (size : Nat) -> Matrix size size ZZPair ->
  (iter : Fin size) -> Matrix size size ZZPair
cofMat Z _ FZ impossible
cofMat Z _ (FS _) impossible

cofMat (S k) mat FZ =
                    replaceAt
                    0
                    (cofRow (S k) 0 mat (tofinNat (k) (S k)))
                    (empMat (S k) (S k))

cofMat (S k) mat (FS y) =
                    replaceAt
                    (FS y)
                    (cofRow (S k) (FS y) mat (tofinNat (k) (S k)))
                    (cofMat (S k) mat (embn k y))

--Inverse of a matrix is the transpose of the cofactor matrix
invMat : Matrix n n ZZPair -> Matrix n n ZZPair
invMat {n} mat = case n of
             Z => []
             (S k) => transpose (cofMat (S k) mat (tofinNat (k) (S k)))

{-
Solving a system of n linear equations:
    a11*x1 + a12*x2 + ... + a1n*xn = b1
    .
    .
    an1*x1 + an2*x2 + ... + ann*xn = bn

-}

--Solves a system ax = b.
--The operation <> is matrix multiplication, defined in Matrix.Numeric
solve : (n : Nat) -> (a : Matrix n n ZZPair) -> (b : Matrix n 1 ZZPair) ->
  Matrix n 1 ZZPair
solve n a b = (invMat a) <> b
