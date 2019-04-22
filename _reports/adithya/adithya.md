---
author: Adithya Upadhya
layout : report
---

### NatUtils
NatUtils.idr

I created the file NatUtils.idr and added proofs useful for working with naturals numbers in the file, such as proofs extending equality and order (as defined by the type LTE on Nat).

#### Possible issues
Currently, all the functions I have added to this file appear to be working.

### Order
Order.idr

I created the file Order.idr to model orders. It currently includes types such as `isReflexive`, `isAntiSymmetric`, `isTransitive`, `isPartialOrder`, `isTotalOrder`.

#### Possible issues
I am not sure whether the type for well-ordering as I have stated it is useful.

#### To be done
1. Defining greatest elements and least elements.
2. Perhaps defining orders with more structure and proving theorems about them.
3. The sorting algorithms could perhaps use these types to sort lists.

### NatOrder
NatOrder.idr

I created the file NatOrder.idr to implement the usual order on the naturals with the type `LEQ`, along with several proofs that are useful for working with them, such as cancellation laws and proofs to show that it is a total order. I have also put in functions: `leqToLTE` `lneqToLT` `lteToLEQ` `ltToLNEQ` to interconvert between them.

#### Possible issues
Currently, all the functions I have added to this file appear to be working.

### Divisors
NatDivisors.idr

1. I modified the definition of divisibility created by Sriram to allow divisibility to be defined only for non-zero natural numbers.
2. I added an algorithm `euclidDivide` that given two natural numbers, returns the quotient and reminder under division with proof that they are the quotient and reminder. Rohit had added one previously, and I removed possible problems with it, with modifications to the algorithm.
3. I have defined a recursive function type `euclidRecursion` that can be used to generate proofs of statements recursively using Euclid's division algorithm.
4. Added proofs involving divisibility such as `dividesAntiSymmetric`, `multipleDivides` `multipleDividesMultiple`.
5. Added the fuction `decDivisible` for the decidability of divisibility. Added helper functions for this including `dividesImpliesGEQ` and `notDivisible`.

#### Possible issues
Currently, all the functions I have added to this file appear to be working.

### GCD
NatGCD.idr

1. Added basic proofs about the GCD such as `gcdUnique` and `divImpliesGCDOne`.
2. Added proofs used to generate the GCD recursively, and used the `euclidRecursion` function type to write `euclidGCD` which returns the GCD of two numbers.
3. Added another recursive function type `euclidGCDExtend` which canbe used to generate recursive proofs involving the GCD. (Most of this can probably done with Bezout's lemma, but since I was working within the natural numbers, I wrote this)
4. Added functions `gcdMult` and `coprimeImpliesDiv` later used in Primes.

#### Possible issues
Currently, all the functions I have added to this file appear to be working. Extending this to Integers would allow some proofs to be easier.

### Primes
NatPrimes.idr

1. Added types `isIrreducible` and `isPrime`, and showed their equivalence with `primeIsIrreducible` and `irreducibleIsPrime`.
2. Added a proof that if an irreducible either divides a number or is coprime to it, as `irreducibleDividesOrCoprime`. (These were intended as helper functions for the decidability of primality)

#### To be done

Decidability of primality. This will require a recursive function that searches for the smallest factor of a number. This is yet to be written. 
