---
author: Sidharth Soundarrajan
layout : report
---

Please fill in this with references to code.

# Project report LTS2019

## Algebra

### [Fields.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Field.idr)

1. made a modified definition `InvExistsNonZero`, the type of proofs that non zero elements of a field have multiplicative inverses.
2. Using this definition for a modified multiplicative inverse, `IsModGrp` is the type of proofs that non zero elements of a field form a group over multiplication.
3. Using this, `IsField` is the type of proofs that a given type with "additions" and "multiplication" appropriately defined on them form a field.

### Finitely Generated Groups [Group.FiniteGenerate.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Group.FiniteGenerate.idr)

1. Created the file on finitely generated groups, with `HasFiniteOrder` proving that an element is finitely generated.
Have to further work on it once primes have been defined with the appropriate properties.

## Number Theory

### [Primes.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Primes.idr)

1. `IsPrime` and `IsComposite` types are the types of proofs that a number is prime or composite respectively.
2. `twoPr` shows that two is a prime to verify the functioning of the `IsPrime` type.
3. Proved that a number cannot be both prime and composite using `notBothPrimeandComp`, which utilises a helper function `aNotEqToMultA` (a not equal to na, where n is greater than 1).
4. `genFact` generates a list of factors of a number along with the proof that they are factors.
5. `isPrimeCalc` and `isCompositeCalc` check for primality of a number computationally.

## Utility files ([Lists.idr](https://github.com/siddhartha-gadgil/LTS2019/blob/master/Code/Lists.idr))
1. Created a file on lists to extract useful results from the `genFact` function mentioned earlier.

### Pending (for now)
1. To show that any number greater than 2 is either prime or Composite. (Partially done, proof that number is composite based on genFact size has been included)
2. To show that every divisor of a number is contained within the `genFact` list.
