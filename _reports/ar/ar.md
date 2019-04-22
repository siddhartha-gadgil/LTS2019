---
author: Abishek Rajan
layout : report
---

## MA 210 : Final Report

## Sorting

I implemented the insertion sort algorithm.

Files: InsertionSort.idr, VectPerm.idr

Everything is total in InsertionSort.idr and VectPerm.idr.

1. I defined the `Insert` function which takes a natural number, a sorted list, and adds it into its appropriate position in the list by comparison. 
2. Using this, I implemented the algorithm through the function `Sort`. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/e23e7f5b2d4df83ab81539da2efc5648da11c130)
3. In the function `CheckSortedVect`, I implemented a Boolean test to check if a Vector is Sorted. This will be upgraded to a proof. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/af78ca7a21e563d6e5c1568818fa6bd53ce08254)
4. For working on permutations, I implemented a function which behaves like the `elem` function (which checks for membership of an element in a list or Vector), but with proof, called `improveElem`. Using this, I compared vectors and found all instances of a particular element of a Vector x in another Vector y with proof with `findIn`.
5. Using the above, I implemented functions which remove an element from a position given a proof that it is at that position `removeElem`.
6. Using this, I implemented some Boolean tests to check whether a Vector is a permutation of another Vector in `recursiveTest` and `listDifference'.
7. In the case where two Vectors have the same elements, the function `PermutationBijection` produces the permutation which takes the Vector x to the Vector y. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/fbf98d4cd75262d2d079240ab0a67d3f7a185372) (contains everything for items 4-7).

#### Remaining

Although the permutation problem is done, integrating it with the sortedness is very difficult.

## Linear Algebra

### One Variable Equations

I solved linear equations in one variable with proof.

Everything is total in Linear.idr.

File: Linear.idr

1. I found with proof that the equation ax = 0 has the solution x = (0,1) when a is not zero in `trivialeqSolver`.[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/1f7cab801381a1f2b7e5c14c712d0893bc62effa)
2. I found with proof that the equation ax + b = 0 has the solution x = (-b,a) when a,b are not zero in `eqSolver`.[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/0d2a515ea420abcfa9b0eb8a91b901d32db2dc01)
3. I found with proof that the equation ax + b = c has the solution x = (c-b,a) when a,b,c are not zero in `GeneralEqSolver`.
[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/55fe7ea3e76e97f6fa4a7de852fec0ba9f3c93e2)
4. I checked whether a Diophantine equation in one variable has an integer solution in the function `IsSolutionZ`. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/393a0a25a43db9975a6db7bc5fe39583a3f8cf7e)

All of the above functions include proofs that the solution (a rational number) is a valid number (nonzero denominator).

Each of these functions had their own associated helper functions to transition between proofs of equalities.

### Diophantine Equations

File: TwoVarDiophEq.idr

Everything is total in TwoVarDiophEq.idr.

The work on two variable Diophantine equations was done in collaboration with Shafil (who had already proven the Bezout Identity).

1. I found with proof whether or not the equation ax + b = c has an integer solution using the function `DiophantineSolver`. Thus, linear Diophantine equations in one variable are complete.
2. For the two variable case, the function `homogeneous` is a helper function which transitions between proofs of equalities in the homogeneous case of the two variable Diophantine equation.
3. I wrote the function `solDifference` which along with `diffIsHomogeneous` proves that if any two pairs satisfy the non-homogeneous equation, then their difference satisfies the homogeneous equation
4. The function `addToSol` is a helper function which is used in conjugation with `differByHomogeneous` (which was done by Shafil, I only defined the function type) to show that any solution is a particular solution + a homogeneous solution.

The Diophantine solver produces a valid rational solution of the equation in case it has no integer solution.

#### Remaining

This could possibly be extended to n-variable Diophantine equations.

### Linear Systems

File: LinearAlgebra.idr

Everything is total in LinearAlgebra.idr.

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

Files: Rationals.idr, FieldAxioms.idr.

Everything is total in Rationals.idr and FieldAxioms.idr

I implemented the non-unique representation of the rational numbers.

1. I defined the rational numbers as a type `ZZPair` (a pair of ZZs, where `ZZ` is a form of integers over which proofs can be done easily). [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/4c261057f0b6b9edf38883015d19137bb9855465)
2. I defined the type for divisibility of Integers `isFactorInt` which was subsequently renamed for the ZZ type.
3. Using this, I defined the arithmetic operations and the inclusion of integers into the rationals, with implementation of proofs wherever necessary that denominators/numerators should not be zero. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/080fd5d0065efffb0afb79720220d35fd9b757c7)
4. I made the function `simplifyRational` work over all ZZPairs by extending the `CalcGCD` function to work over pairs of `ZZ` instead of pairs of `Nat`. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/429fd11b09106392452f09a37a97eb25e7ecf189)
5. I started proofs that the sum of a rational and its additive inverse is the additive identity. [Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/ac3ee364e84b3aa82fb602c401499e42bfc8cc0f)
6. The function `CheckIsQuotientZ` checks if the rational number is equivalent to an integer with proof (for example, 12/4 is 3). 
[Link Here](https://github.com/siddhartha-gadgil/LTS2019/commit/97bf91ac84a01a63e0d6fc58c023a600992cb134)
7. I implemented simplification of rational numbers using a theorem that Shafil proved (dividing two numbers by their GCD makes them coprime) in the function `simplifyWithProof` which returns a simplified rational along with a proof that it is simplified.
8. I implemented a type representing equalit of rational numbers `EqRat` which sets two rational numbers (a,b) (c,d) as equal if ad=bc.
9. I proved the analogues of reflexivity, symmetry, and transitivity for this type.
   1. `EqRatRefl` creates an `EqRat` element of every valid (a,b) (a,b).
   2. `EqRatRefl` creates an `EqRat` element of (c,d) (a,b) given an `EqRat` element of (a,b) (c,d) (the analogue of symmetry)
   3. `EqRatTrans` creates an `EqRat` element of (a,b) (e,f) given an `EqRat` element of (a,b) (c,d) and an `EqRat` element of (c,d) (e,f). (all of the constructions are done only in the case of valid rational numbers).
10. Using the above, I proved associativity and commutativity of addition and multiplication, and the existence of (both left and right) identities and inverses for addition and multiplication, which involved a lot of `rewrite` statements. (which is most of the field axioms).
11. The above proofs (with explanations) can be found in the file FieldAxioms.idr
   - `addIdRightEqRat` and `addIdLeftEqRat`
   - `multIdRightEqRat` and`multIdLeftEqRat`
   - `addInverseLeftEqRat` and `addInverseRightEqRat`
   - `multInverseLeftEqRat` and`multInverseRightEqRat`
   - `plusCommQEqRat`
   - `multCommQEqRat`
   - `plusAssocQEqRat`
   - `multAssocQEqRat`
   
   
#### Remaining

The distributive laws need to be proved. In addition, a rational number is different from a pair of integers in the respect that the second integer should not be zero. In every function which has an argument involving `ZZPair`, the following argument is usually a proof that the second integer is nonzero. I believe that a new data type (called QQ) could be created, consisting of a ZZPair and a proof that the second integer is nonzero. It would be cleaner to define functions using such a data type and would possibly be easier to use in computation/as arguments to other functions. 


#### Helper files (ZZUtils, etc)

I added various helper functions to these. In these files, everything is total.
