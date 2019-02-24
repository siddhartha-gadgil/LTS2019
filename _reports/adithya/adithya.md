---
author: Adithya Upadhya
layout : report
---

### NatUtils
NatUtils.idr

I created the file NatUtils.idr and added proofs useful for working with naturals numbers in the file, such as proofs extending equality and order (as defined by the type LTE on Nat). Shafil has also contributed proofs to this file.

#### Possible issues
Currently, all the functions I have added to this file appear to be working.

#### To be done
The cancellation law for multiplication. I intend to use the trichotomy of natural numbers using the order defined in the file NatOrder.idr to complete this soon.

### Order
Order.idr

I created the file Order.idr to model orders. It currently includes types such as `isReflexive`, `isAntiSymmetric`, `isTransitive`, `isPartialOrder`, `isTotalOrder`.

#### Possible issues
I am not sure whether the type for well-ordering as I have stated it is useful.

#### To be done
1. Defining greatest elements and least elements.
2. Perhaps defining orders with more structure and proving theorems about them. (which will require some reading on my part)
3. The sorting algorithms could perhaps use these types to sort lists.

### NatOrder
NatOrder.idr

I created the file NatOrder.idr to implement the usual order on the naturals with the type `LEQ`, along with several proofs that are useful for working with them, such as cancellation laws and proofs to show that it is a total order. I have also put in two functions `leqToLTE` and `lteToLEQ` to interconvert between them.

#### Possible issues
Currently, all the functions I have added to this file appear to be working.

#### To be done
1. The cancellation law for multiplication. I intend to use the trichotomy of natural numbers using the order defined in this file to complete this soon, same as the cancellation law across equality.
2. Perhaps replace the usage of `LTE` with `LEQ` in other functions, since it also holds information of the difference between two numbers, making it more convenient to use.

### GCD
gcd.idr

1. I modified the definition of divisibility created by Sriram to allow divisibility to be defined only for non-zero natural numbers.
2. I added an algorithm `euclidDivide` that given two natural numbers, returns the quotient and reminder under division with proof that they are the quotient and reminder. Rohit had added one previously, and I removed possible problems with it, with modifications to the algorithm.

#### Possible Issues
I am not entirely sure if defining divisibility only for non-zero divisors is necessary. The possible problem with this is that only 0 is divisible by 0, but cancellation will not yield equality. If it turns out that it will not be necessary for later use, it can be removed without too much hassle, hopefully.

#### To be done
An algorithm that returns the GCD of two natural numbers with proof that it is the GCD.
