---
author: Vrunda Rathi
layout : report
---


#**Q.idr**
Defined the data type *SimpQ* as a transversal group for Rationals, where each element of the type contains the proof that the numerator and denominator are coprime. The proof was included using **Erasure** and when implemented correctly (which I could not manage to do) will not require equality of proofs, when proving equality.

Made functions to take any Rational number *Q* to its simplified form *SimpQ*. 

Defined addition, multiplication over *Q*. Proved that zero is the additive identity and one is the multiplicative identity in the form pre-defined in **Monoids.idr**. Proved commutativity of addition and multiplication over *Q*

Defined addition and multiplication over *SimpQ* using *AddQ* and *multQ*


#**Rats.idr**
Defined addition, multiplication and the equality function for the data type *Rats* defined in class, as a better definition for the field of Rational numbers as all the deinitions in **Field.idr** require the proof to be within the type.

Abandoned this definition later, as it required the equality of proofs at every stage which is very cumbersome.

#**Rationals.idr**
Defined the type *isFactorZZ* (Was later deleted as an identical type *isDivisibleZ* was created in **Divisors.idr** and was used more frequently)


#**ZZUtils.idr**

Defined auxillary functions required to prove stuff in *Q.idr*, *Rationals.idr* etc.


#**bezout.idr**

proved that if p|a and p|b , p|(a+b).

#**NatUtils.idr**

proved auxillary functions to be used in *bezout.idr*











Please fill in this with references to code.
