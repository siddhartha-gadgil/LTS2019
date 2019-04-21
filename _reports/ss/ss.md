---
author: S Sriram
layout : report
---

## Contributions (Final)
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

#### NatUtils
1. I added one lemma which given `LTE a b` and `LTE c d`, returns the type `LTE (a+c) (b+d)`. This is useful in an independent context as well.

#### Primes
1. I created the `Primes` module and defined some useful lemmas and definitions.
  - I created a divisibility type with slight modifications to ensure that it does not admit zero divisors (originally created in __gcd.idr__)
  - I implemented a type `totOrdNat`, which, given `a`, `b` : `Nat` returns a type with a proof if either `a = b`, `a < b` or `a > b`
  - I defined various other functions as auxiliary for the `decDiv` function, but are useful in their own right in providing contradictions and contrapositives.
2. Using all the helper functions defined previously, I defined a `decDiv` function that given `a`, `b`, returns a `Dec (isDivisible a b)` type with proofs and contradictions depending on the values.
  - All cases are complete and `decDiv` is total as well (Required a lot of helpers and extensive use of `rewrite`s for the last case, and was _very difficult_). This will be an important building block for the rest of the _Primes_ project. This was completed in commit [Primes.idr](https://github.com/siddhartha-gadgil/LTS2019/pull/186/commits/66aad165c174a867ceb7032e8fed93cc327e5fb6)
  - Lots of the named helper functions are useful in an independent setting as well; with respect to divisibility.
3. I started work on Prime factorization. Some of the important functions: 
  - `factor2` returns two factors of a number such that the first one is prime. (Not proved yet)
  - `factorise` factors a number completely with proof that the factors fold back under multiplication to generate the original input.
  - (`List Nat` needs to be augmented to be `List (n : Nat ** isPrime n)` for the final version)
  These were done in commits [Prime.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/0703c874a001167014734bce2c7541ed2d8b1f11#diff-f7930854c023cabc916b04537cd33585) and  [PrimeApple.idr](https://github.com/siddhartha-gadgil/LTS2019/commit/251328143d1b5797105bda7651e76037741c25a0#diff-f7930854c023cabc916b04537cd33585)
