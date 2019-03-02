---
author: Abishek Rajan
layout : report
---

## MA 210 : Midterm Report

## Sorting

I implemented the insertion sort algorithm.

File: InsertionSort.idr

1. I defined the `Insert` function which takes a natural number, a sorted list, and adds it into its appropriate position in the list by comparison. 
2. Using this, I implemented the algorithm through the function `Sort`. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/e23e7f5b2d4df83ab81539da2efc5648da11c130)
3. In the function `CheckSortedVect`, I implemented a Boolean test to check if a Vector is Sorted. This will be upgraded to a proof. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/af78ca7a21e563d6e5c1568818fa6bd53ce08254)

#### Remaining

It remains to be proved that any Vector which is the output of `Sort` is a sorted vector. Also, it needs to be shown that `Sort` simply permutes the elements of a Vector.

## Linear Algebra

### One Variable Equations

I solved linear equations in one variable with proof.

File: Linear.idr

1. I found with proof that the equation ax = 0 has the solution x = (0,1) when a is not zero in `trivialeqSolver`.[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/1f7cab801381a1f2b7e5c14c712d0893bc62effa)
2. I found with proof that the equation ax + b = 0 has the solution x = (-b,a) when a,b are not zero in `eqSolver`.[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/0d2a515ea420abcfa9b0eb8a91b901d32db2dc01)
3. I found with proof that the equation ax + b = c has the solution x = (c-b,a) when a,b,c are not zero in `GeneralEqSolver`.
[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/55fe7ea3e76e97f6fa4a7de852fec0ba9f3c93e2)
4. I checked whether a Diophantine equation in one variable has an integer solution in the function `IsSolutionZ`. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/393a0a25a43db9975a6db7bc5fe39583a3f8cf7e)

Each of these functions had their own associated helper functions to transition between proofs of equalities.

#### Remaining

To make the program run more smoothly, I need to implement a function which takes a,b,c as input and based on non-zero considerations, uses the appropriate solver to output a solution with proof. Also, simplification of rationals needs to be done (will require the GCD with proof from another project). Also, the Diophantine equation needs a proof that it is a solution, but this will also require the GCD with proof to say that a rational number is actually an integer in disguise.

### Linear Systems

File: LinearAlgebra.idr

I implemented the Gauss-Jordan process which due to its versatility has many applications.

1. Implemented the basic elementary operations on matrices. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/7a12fcc8932277255b89ad5143c43e0d5c01b7cc)
   1. Swap Rows in `Swap_Rows`
   2. Scale a Row in `Scale_Row`
   3. Subtract a multiple of a row from another in `Row_Operation`
2. I used these to appropriately convert elements to zero in a matrix with `MakeElementZero`. 
3. The function `MakeColumnZero` uses this technique to fill columns with zeroes. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/1adc1e651b7b7f3d0f58505793e06ec13e93ae50)
4. The function `UpperTriangularize` is a helper function for `UpperTriangularForm` which converts a matrix to Upper Triangular Form.[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/a2a2b35f5907291b1aeecccc7f752f20cf9c84fe)
5. I found a diagonal form of a matrix using `DiagonalForm` using the above and extended it to convert any matrix to an identity (if all the diagonal elements are non-zero) in `TotalReduce`. If not, the zero rows are left as they are while the others are reduced. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/a302e8f2a1708d4dad8b5b515a9bb4435fdd86c1)
6. I found the magnitude of the determinant using `DetUpToSign` on the diagonal form of a matrix. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/650094ed4a5784dc8220081b785741d35da06788)
7. Also, as computation time signifcantly increases with larger numbers, I added in some functions, culminating in `simplifyMatrix`, which convert a matrix to simplified form. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/abd348d60ffca6de7adc9b87ceebb493d21aa375)

#### Remaining

Here are a few possible applications of this process.

1. Solving linear systems (from upper triangular form, or from diagonal form) with proof.
2. Calculating the inverse of a matrix (and proving basic facts about it).
3. Finding the rank of a linear transformation, showing that it is independent of the choice of basis.

## Rationals

I implemented the non-unique representation of the rational numbers.

1. I defined the rational numbers as a type `ZZPair` (a pair of ZZs, where `ZZ` is a form of integers over which proofs can be done easily). [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/4c261057f0b6b9edf38883015d19137bb9855465)
2. I defined the type for divisibility of Integers `isFactorInt` which was subsequently renamed for the ZZ type.
3. Using this, I defined the arithmetic operations and the inclusion of integers into the rationals, with implementation of proofs wherever necessary that denominators/numerators should not be zero. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/080fd5d0065efffb0afb79720220d35fd9b757c7)
4. I made the function `simplifyRational` work over all ZZPairs by extending the `CalcGCD` function to work over pairs of `ZZ` instead of pairs of `Nat`. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/429fd11b09106392452f09a37a97eb25e7ecf189)
5. I started proofs that the sum of a rational and its additive inverse is the additive identity. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/ac3ee364e84b3aa82fb602c401499e42bfc8cc0f)

#### Remaining

The proof of the above result needs the GCD to be implemented (for `simplifyRational` to output a proof that the rational is in fact simplified). Also, the corresponding proof involving the multiplicative inverse will require this as well. Using the properties of `ZZ`, the distributive law can be the next step.
