---
author: Shafil Maheenn
layout : report
---

## Report on contributions to Projects in LTS 2019
#### Merge
1. I implemented the `merge1` function that merges two sorted lists such that
   the resulting list is sorted in [Merge.idr ](https://github.com/siddhartha-gadgil/LTS2019/commit/ad53e8b17293af28066f32bf8a35ef216d5c7f0b)

## Bezout's lemma
1. I implemented an function, `Bezout`  that (given two natural numbers a and b) performs  Euclidean algorithm and returns two integers x and y such that d = ax +by
where d = GCD (a,b) in [Bezout.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/ff3a44a60c4ba678eb03dae47b46205fa7159e67)
2. inplemented `EuclList` which gives a list of quotients and remainders when applying Euclid's algorithm to two natural numbers a and b. [Link here](https://github.com/siddhartha-gadgil/LTS2019/commit/f7f05adfce47e5ccb93b231ec000c576f3d217b1). This commit consists of both my code and Rohit's code as Rohit had accidentally put his code outside the code folder.


## Divisors
1. Implemented `IsDivisibleZ` and `IsCommonFactorZ`  types which are based on the corresponding data types for natural numbers created by Sriram and Rohit respectively. Also the function `oneDiv` is based on Sriram's code. The rest of the code in [Divisors.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Divisors.idr) is my code as of the time of writing this report.
2. I proved a few theorems about divisibility of integers and about GCD.

## ZZ
1. I had to create many auxiliary functions and data types in [ZZ.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/ZZ.idr)  for use in Divisors.idr. Some of these are
2. Implemented `LTEZ` type which is the **less than or equal to** type for integers. [Link here](https://github.com/siddhartha-gadgil/LTS2019/commit/a9260c3fc1d4dfcbe515705cc7d670d50b260d8d)

3. Proved antisymmetry of LTE type for natural numbers and LTEZ type for integers. [Link here](https://github.com/siddhartha-gadgil/LTS2019/commit/a9260c3fc1d4dfcbe515705cc7d670d50b260d8d)
4. Implemented IsPositive data type and `DecidePositive` ,a function that returns whether an integer is positive or not with proof.
5. `isLTEZ` function that works just like isLTE for Nat
6. And a few other auxiliary functions.
6. **I copied some of Vrunda Rathi's** code into `ZZ.idr` when I was fixing some errors [Link here](https://github.com/siddhartha-gadgil/LTS2019/commit/faa807e50e658f1a54c8640b85ffce140715eaa2)

## [gcd.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/gcd.idr)
1. Implemented `PlusDiv` and `MultDiv` for natural numbers which were later changed to integers in `Divisors.idr`.[Link here](https://github.com/siddhartha-gadgil/LTS2019/commit/be28efe9bbe3c28da17edadb3d7770034a901178)
2. Made the `euclDivide` function total [Link here](https://github.com/siddhartha-gadgil/LTS2019/commit/11b00d349f82cee4c88aad11c258e9979bcb16f3)

## [Graph.idr ](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Graph.idr)
1. The `AdjacentsAreConnected` function returns a proof that 2 adjacent vertices are connected **by an edge** or nothing if they are not connected.
2. `EdgeisPath` function proves that adjacent vertices (i.e. vertices that have an edge between them) are connected
3. `ConnectedComponents` takes a simple graph (symmetric matrix with 0's and 1's) and returns a list of connected components as a list of lists of Nats
4. `PathWithProof` function returns a **simple path** between  two vertices if there is a path with proof or Nothing if there is no path. Here a path is represented as a List of vertices that were traversed.
5. Most of the functions used are not total, and they will work properly only as long as the **adjacency matrix of a simple graph** is given as input.
6. The file [Graphexamples.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Graphexamples.idr) has a few examples of how to use these functions.
## GCD of integers
1.The file [GCDZZ.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/GCDZZ.idr) has a function `gcdZZ` which returns the gcd of two integers with proof given that not both of them are zero

# Post Midterm
## [Divisors.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Divisors.idr)
1.The function `divideByGcdThenGcdOne` proves that
gcd ( (a/gcd(a,b)),(b/gcd(a,b)) ) =1

## GCD of integers [GCDZZ.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/GCDZZ.idr)
1. The function `bezoutCoeffs` takes two integers and a proof that they are not both zero and returns the GCD of the two integers, a proof that it is the gcd and the Bezout coefficients with proof.
2. The function, `gcdOfMultiple` proves the theorem that if m>0 and a and b are not both zero, then gcd(ma,mb) = m \*gcd (a,b)
3. The function, `caCoprimeThencDivb` proves the theorem that if c|ab and gcd (a,c) =1 , then c|b
4. Introduced `GCDZr` type which defines GCD as the greatest of the common divisors and proved the equivalence of the two definitions in the functions `GCDZImpliesGCDZr` and `GCDZrImpliesGCDZ`
5.  Introduced a `SmallestPosLinComb` which defines the smallest positive linear combination of two integers. Showed that this is equivalent to `GCDZ` in the functions  `gcdIsSmallestPosLinComb` `smallestPosLinCombIsGcd`.
6. `gcdIsLinComb` function proves that gcd (a,b) is a linear combination of a and b .

## [decDivZ.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/decDivZ.idr)
1. The function `decDivisibleZ` checks whether one integer is divisible by the other with proof. (It depends on Sriram's decDiv function.) It works for any two integers.

## [ZZUtils.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/ZZUtils.idr)
1. Defined types  , `IsNonNegative`, `IsNegative`, `NotZero` for integers.
2. Proved multiplication and addition cancellation laws for integers.
3. `productOneThenNumbersOne` function  proves  that if (a\*b=1) then either (a=1,b=1) or (a=-1,b=-1)
3. There are also other useful functions in `ZZUtils`

## [TwoVarDiophEq.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/TwoVarDiophEq.idr)
 (Done in collaboration with Abhishek)
1. `aByd` and `bByd` functions extract the values of a/gcd(a,b) and b/gcd(a,b) respectively from the definition of GCDZ.
2.  Implemented `findAllSolutions` function which  given three integers a, b and c, it outputs either
a proof that c = xa +yb is impossible or
a proof that all integers x and y satisfy the equation (this happens when a=b=c=0)
or 4 integers x1 , y1 , pa and pb such that for any integer k,
x=x1+k\*pa  y=y1+k\*pb is a solution of c=xa+yb
and whenever c=xa+yb ,there exists an integer, k such that
 x=x1+k\*pa  y=y1+k\*pb.
