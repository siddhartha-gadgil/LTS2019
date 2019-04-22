---
author: Rohit Kumar
layout : report
---

## Algebra :

Added the definitions of :-

1. An Intergal Domains
2. An Euclidean Norm over an Integral Domain
3. An Euclidean Domain

Added a file called Module.idr and added

  1. The definitions of the types for distributivity of the action of the ring on the module
  2. Added the definition for the IsLeftModule type
  3. Added functions to recover the individual Distributivity types from the IsLeftModule type.
  4. Added functions to recover the zero of the module from the IsLeftModule type
  5. Proved that r.0 = 0 (Action of any ring element on zero is zero)
  6. Proved that 0.m = 0 (Action of zero of the ring on any element is zero)

## Number Theory :

  1. Provided a partial proof of Euclid's Division Lemma (Existence of Quotient and Remainders when we divide a natural number by another),      which was later improved upon by other people. (This also had 5 auxiliary proofs, which include Trichotomy of the order on integers        and Anti-symmetry of LTE)
  2. Provided the definitions of a Common Factor Type and a GCD Type. (I did not prove that such a GCD would be unique)
  3. Proved the following facts about the GCD (This had about 4 auxiliary proofs): (Which was also later improved upon by other people)
     1. If d is a GCD of a and b, then d is also a GCD of a + b and b.
     2. If d is a GCD of a + b and b, then d is also a GCD of a and b.
     3. If d is a GCD of a and b, then d is also a GCD of b and a.
