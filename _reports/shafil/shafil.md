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
2.Made the `euclDivide` function total [Link here](https://github.com/siddhartha-gadgil/LTS2019/commit/11b00d349f82cee4c88aad11c258e9979bcb16f3)

## [Graph.idr ](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Graph.idr)
1. The `AdjacentsAreConnected` function returns a proof that 2 adjacent vertices are connected **by an edge** or nothing if they are not connected.
2. `EdgeisPath` function proves that adjacent vertices (i.e. vertices that have an edge between them) are connected
3. `ConnectedComponents` takes a simple graph (symmetric matrix with 0's and 1's) and returns a list of connected components as a list of lists of Nats
4. `PathWithProof` function returns a **simple path** between  two vertices if there is a path with proof or Nothing if there is no path. Here a path is represented as a List of vertices that were traversed.
5. Most of the functions used are not total, and they will work properly only as long as the **adjacency matrix of a simple graph** is given as input.
6. The file [Graphexamples.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Graphexamples.idr) has a few examples of how to use these functions.
## GCD of integers
1.The file [GCDZZ.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/GCDZZ.idr) has a function `gcdZZ` which returns the gcd of two integers with proof given that not both of them are zero
