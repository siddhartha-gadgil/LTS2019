---
author: Adithya Upadhya
layout : report
---

### NatUtils
I have created the file NatUtils.idr and added proofs useful for working with naturals numbers in the file, such as proofs extending equality and order (as defined by the type LTE on Nat). Shafil has also contributed proofs to this file.

### Order
I have created the file Order.idr to model orders, and I have proved a few basic theorems regarding these.

### NatOrder
I have created the file NatOrder.idr to implement the usual order on the naturals, along with several proofs that are useful for working with them, such as cancellation laws and proofs to show that it is a total order.

### GCD
I have modified the definition of divisibility created by Sriram to allow divisibility to be defined only for non-zero natural numbers. (I am not entirely sure if this is necessary. The possible problem with this is that only 0 is divisible by 0, but cancellation will not yield equality. If it turns out that it will not be necessary for later use, it can be removed without too much hassle, hopefully.)

Further, I have added an algorithm that returns the quotient and reminder under division with proof. Rohit had added one previously, and I removed possible problems with it, with modifications to the algorithm.  
