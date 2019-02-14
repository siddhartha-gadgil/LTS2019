---
author: Abishek Rajan
layout : report
---

## Sorting

File: InsertionSort.idr

I implemented the insertion sort algorithm.

1. I defined the `Insert` function which takes a natural number, a sorted list, and adds it into its appropriate position in the list by comparison.
2. Using this, I implemented the algorithm through the function `Sort`.

## Linear Algebra

### One Variable Equations

I solved linear equations in one variable with proof.

File: Linear.idr

1. I found with proof that the equation ax = 0 has the solution x = (0,1) when a is not zero in `trivialeqSolver`.
2. I found with proof that the equation ax + b = 0 has the solution x = (-b,a) when a,b are not zero in `eqSolver`.
3. I found with proof that the equation ax + b = c has the solution x = (c-b,a) when a,b,c are not zero in `GeneralEqSolver`.

Each of these functions had their own associated helper functions to transition between proofs of equalities.

#### Remaining

To make the program run more smoothly, I need to implement a function which takes a,b,c as input and based on non-zero considerations, uses the appropriate solver to output a solution with proof. Also, simplification of rationals needs to be done (will require the GCD with proof from another project). Also, GeneralEqSolver can be used to solve Diophantine equations in one variable.

### Linear Systems

File: LinearAlgebra.idr

I implemented the Gauss-Jordan process which due to its versatility has many applications.

1. Implemented the basic elementary operations on matrices.
   1. Swap Rows in `Swap_Rows`
   2. Scale a Row in `Scale_Row`
   3. Subtract a multiple of a row from another in `Row Operation`
2. I used these to appropriately convert elements to zero in a matrix with `MakeElementZero`.
3. The function `MakeColumnZero` uses this technique to fill columns with zeroes.
4. The function `UpperTriangularize` is a helper function for `UpperTriangularForm` which converts a matrix to Upper Triangular Form.
5. I found a diagonal form of a matrix using `DiagonalForm` using the above and extended it to convert any matrix to an identity in `MakeIdentity`.
6. I found the magnitude of the determinant using `DetUpToSign` on the diagonal form of a matrix.

#### Remaining

Implementation of simplification of matrix elements (like `simplifyRational`) should be done to make the program run more quickly. Apart from that, here are a few possible applications of this process: 

1. Solving linear systems (from upper triangular form, or from diagonal form) with proof.
2. Calculating the inverse of a matrix (and proving basic facts about it).
3. Finding the rank of a linear transformation, showing that it is independent of the choice of basis.

## Rationals

I implemented the non-unique representation of the rational numbers.

1. I defined the rational numbers as a type `ZZPair` (a pair of ZZs, where `ZZ` is a form of integers over which proofs can be done easily).
2. Using this, I defined the arithmetic operations and the inclusion of integers into the rationals, with implementation of proofs wherever necessary that denominators/numerators should not be zero.
3. I made the function `simplifyRational` work over all ZZPairs by extending the `CalcGCD` function to work over pairs of `ZZ` instead of pairs of `Nat`.
4. I started proofs that the sum of a rational and its additive inverse is the additive identity.

#### Remaining

The proof of the above result needs the GCD to be implemented (for `simplifyRational` to output a proof that the rational is in fact simplified). Also, the corresponding proof involving the multiplicative inverse will require this as well. Using the properties of `ZZ`, the distributive law can be the next step.
