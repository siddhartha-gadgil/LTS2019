---
author: Arka Ghosh
layout : report
---

## Groups

#### Definitions

1. Defined _Monoid_ in the file `Monoid.idr` by the type
   `IsMonoid` in the file `Monoid.idr`
2. Defined _Group_ in the file `Group.idr` by the type
   `IsGroup` in the file `Group.idr`.
3. Defined _Abelian Group_ by the type `IsAbelianGrp`.
  -- ask Chinmoy if he did it first
4. Corrected the definition of _Image of a homomorphism_
  given by Chinmoy, in the file `Quotient_Group.idr`.

#### Properties
Proved the following property for groups in the file
`Group_property.idr`.
1. Identity is unique for groups. (`Group_property_1`)
2. Inverse of an element is unique. (`Group_property_2`)
3. b = c implies a\*b = a\*c. (`Group_property_3`)
4. a\*b = a\*c implies b = c. (`Group_property_4`)
5. b = c implies b\*a = c\*a. (`_Group_property_5`)
6. b\*a = c\*a implies b = c. (`_Group_property_6`)
7. One sided inverse is two sided inverse. (`Group_property_7`)
8. If f : g -> h is group homomorphism then
 f(inv(a)) = inv(f(a)) (Proof has _holes_ to fill)
 (`Group_property_8`)

### Quotient Groups

All are done in the file `Quotient_Group.idr`.
2. Defined the type of `Coset` of an element.
1. Given the type which represents that a particular element is in the Coset of an element by `Is_in_Coset`.
3. Given the type of the proposition - If b is in the coset
   of a, then a is in the coset of b.
4. Given the type of the proposition - A proof that
  _Coset(a) * Coset(b)_ and _Coset(a*b)_ are equal as sets.



## Rings

Defined rings in the file `Ring.idr`.

## Sorting with proof

#### Type of sorted vectors
Defined the type of sorted vectors by the type
`SortedVect` in the file `sorting_with_proof.idr`


#### Permutation

1. Defined permutations as bijections by two functions `PermB`
   and `Perm2` in the file `permutation.idr`.
2. Defined application of a permutation by the function
  `applyFun`in the file `permutation.idr`.
3. Defined a type `Finite` and proved that it is _equivalent_
   to the type `Fin`. `Finite` is easier to work with as it
   makes the size explicit.
4. Defined permutations by constructors by the type `PermC`
   in the file `perm_cons.idr`.
