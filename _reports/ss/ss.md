---
author: S Sriram
layout : report
---

## Contributions
#### Rationals
1. I implemented a function to simplify rationals and added a few more auxiliary functions to [Rationals.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/f3333ebc609f4807cebee152a4b4691fdff298bb)
2. I updated some of the types from `Integer` to `ZZ`, and provided casts for ease of use.

#### Linear Equations
1. I created the initial framework for solving linear equations, in the commit [Linear.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/55bd91abd5b018088f85c3af26941d2d7a788f11)
2. I completed the last case in the proof (which was _difficult_), and finished the single equation solver with proof, in the commit [Linear.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/4d81e7e8dfb585de2e09997a5537b62092fbe4b5)

#### GCD
1. I defined a divisibility type, which is useful for multiple purposes, and is present in different files as well (introduced in commit [gcd.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/62a2c8e960d6ecf9956b21e8d3037b0f71ac3521))

#### Solving multiple linear Equations
1. I created the file MultiSolver, (originally Linear.MultiSolver) and defined a bunch of useful computations required to solve a system of linear equations.
  - I defined minors and cofactors for a `n x n` square matrix with entries as `ZZPairs` and created the adjoint matrix to help make inverses.
  - I defined the inverse for a matrix (only the case where the determinant is non-zero)
  - I used the inverse to solve a system of linear equations, again only when the system is consistent.
  - This was in the commit [Linear.MultiSolver.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/228398917996fa51a64aa4eb5d312d59dc796a63)
2. I defined the `Num` and `Neg` interfaces for `ZZPairs`, which are useful, as inbuilt functions require input of such an interface. This was mostly in commit [Linear.MultiSolver.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/74a47fb42abdeb7281f7524a1460922cb7fb8bff)
