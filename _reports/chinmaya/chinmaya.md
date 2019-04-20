---
author: Chinmaya Kausik
layout : report
---

All functions defined are now total.

## Groups

### Definitions

1. Defined _Abelian Groups_ by the type `IsAbelianGrp` in the file `Group.idr`
2. Defined the type of _Injective functions_ in the file `Group.idr` by the type
   `Inj` in the file `Group.idr`
3. Defined the data type `Group` for _Groups_ in `Group.idr`
3. Defined _Homomorphisms_ in the file `Group.idr` by the type
   `Hom` in the file `Group.idr`
4. Defined _Subgroups_ in the file `Group.idr` by the type `Subgroup`
5. Defined _Self-Conjugate Subgroups_ in the file `Group.idr` by the type `NSub`

## Cosets and Quotienting

### Definitions

1. Defined _Transversals_ in the file `Cosets.idr` using the type `IsTransversal` (composed of types `CosetInj` and `CosetAll`)
2. Defined the data type for _Transversals_ using the type `Transversal` in the file `Cosets.idr`

### Functions and Proofs

1. Defined _Coset Multiplication_ using the function `MulTrans` in the file `Cosets.idr`
2. Generated the _Representative_ of an element of group in a given transversal using the function `repgen` in the file `CosetRep.idr`
3. Proved that _Coset Representatives_ thus generated for the embedding of a transversal in its underlying group are the same as the transversal elements. This is, in some sense, the uniqueness of coset representatives.

## Rings

### Definitions (in the file `Ring.idr`)

1. Corrected the definition of the type `IsDistributive` 
2. Corrected the definition of the type `IsRing` to match apparent intentions and for defining ideals.
3. Defined data types for _Rings_, _Commutative Rings_, _Useful Rings_, _Rings with Identity_, _Integral Domains_, _Euclidean Domains_ and _PID's_ (also defined the raw type for PID's) in the file
4. Defined some of the functions that show the appropriate relations between these types (e.g `URingisCRing` generates the data type of a commutative ring structure from a useful one on a given type) 
5. Defined some of the functions that extract the ring operations and multiplicative identity from elements of these data types (e.g. `Ring_Mult_identity` provides the multiplicative identity of a ring with identity)
6. Defined _Ring Homomorphisms_ between general rings through the type `RHom`
7. Defined _Ring Homomorphisms_ between rings with identity through the type `IRHom`
8. Defined _Ideals_ of rings through the type `IsIdeal`
9. Defined _Principal Ideals_ through the type `IsPrincipalIdeal`
10. Defined _PID's_ through the type `IsPID`

### Functions and Proofs (in the file `Ring.Properties.idr`)

1. Proved that if a+a = a in a given ring, then a = 0
2. Proved that a*0 = 0 and 0*a = 0
3. Proved that if _f_ is a ring homomorphism between general rings (without multplicative identities), then f(0) = 0
4. Proved that if _f_ is a ring homomorphism between rings with multiplicative identities, then f(0) = 0

### Examples (in the file `RingExamples.idr`)

1. Proved that _ZZ_ forms a ring under + and *

## Arithmetic in Base n

Defined the inductive type `Base` (with argument `n`) of numbers in _Base n_

### Functions and Algorithms (in the file `Basen.idr`)

1. Defined the function `Rev` (and an auxiliary `Revonto`) that _Reverses_ the base n representation of a number
2. Defined the function `concat` that _Concatenates_ two numbers in base n
3. Defined the functions `tonatFin` and `tonat` that _Convert_ a number in Fin n and Base n respectively to their natural number equivalents
4. Defined the functions `tofinNat` and `tofin` that _Convert_ a natural number to its modular Fin n reduction and representation base n respectively
5. Defined the function `Eucl` that finds the _Quotient and Remainder_ for two numbers along the way
6. Defined the function `embn` that _Vertically Embeds_ a member of Fin n in Fin (S n)
7. Defined the function `Predec` that finds the _Predecessor_ in Fin n of a number in Fin (S n) if it is not equal to n itself.
8. Defined the function `addfin` that _Adds_ two numbers in Fin n
9. Defined the function `addfinlist` that _Adds_ two numbers in base n
10. Defined the function `mulfinList` that _Multiplies_ two numbers in base n

## Lists

### Proofs (in the file `Lists.idr`)

1. Proved that the reverse function for lists is, in some sense, _Pseudo-contravariant with concatenation_ through the function `reviscontra`
2. Proved that the  reverse function for lists is _Self-Inverse_ through the function `reveq`

## Nat Utilities

### Proofs (in the file `NatUtils.idr`)

1. Proved that a witness of LTE m n implies a witness of (lte m n = True)
