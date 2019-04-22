---
author: Nabarun Deka
layout : report
---

### 1. Quicksort function
I created a function (**partitionVect**) that accepts a pivot and a vector and partitions the vector into two vectors according to whether the elements are smaller than or larger than the pivot, and returns the lengths of the parts as well as a proof that the sum of their lengths is equal to the length of the original vector.

### 2. Mergesort
Shafil had written an incomplete code that had a merge function to merge to sorted vectors into one sorted vector. I completed the code by creating a mergesort function. The work I did for this is :

  * I created two functions that partition a Vector into two parts, the parts being equal if the length of the vector is even (**halfVectEven**), and the parts being unequal if the length of the vector is odd (**halfVectOdd**).
  *  I created a mergesort function that splits cases on whether the length of the Vector is Even or Odd, partitions it by the two functions I created earlier, and then applies mergesort recursively to both the parts.


This mergesort function was not total however, because the **Vecttake** function that Shafil defined was not total. So I made it total by adding a condition that the length of the Vector that we take is LTE the length of the original Vector. To make the rest of the auxiliary functions total, I had to prove a lot of lemmas and Theorems (eg : **nLTESn**,**halfnLTEn**, etc.). However, I was unable to make the proof that if (a = b), then (a is LTE b) total.

I also started working on proving that the result of the mergesort function is sorted. For this, I thought of the following strategy :

  * First, prove that the merge (**merge1**) function returns a sorted Vector. For this, I proved the auxiliary theorem that if I have a sorted Vector, v, and an element, x, which is LTE the first element of v, then the vector (x :: v) is also sorted.
  * Use the auxiliary theorem to construct a recursive prove that merge1 returns a sorted Vector.
  * Use this to Prove that mergesort returns a sorted Vector.


### 3. Completing Quicksort


*I provided a quicksort function (for Lists) that sorts and also provides a proof that the output List is sorted and is a permutation of the input List.
*I started by creating types for a Preorder and a Totalorder.
*Then I created a type (**ForAll**) that acts as a proposition that all the elements of a list satisfy some property p. I proved some theorems on this property (eg. mapping a list to another preserves the forall property, concatenation preserves it etc.)
*I defined a LTE type for length of lists just like LTE for nat. I proved a few simple lemmas on this lte property of lists (**lemma1**, **lemma2** and **lemma3**). * I created types for a sorted list and permutation of a list. I proved theorems on permutation
* I created a partition function (**partitionFunc**) that partitions the list and gives proof that the concatenation of the parts is a permutation of the original list.
* I created a partition function (**ordPartition**) that partitions based on a total order and gives a proof that the elements in the two parts are ordered according to the pivot
* Finally, I created an auxiliary function that will help perform quicksort and give proofs that the output is sorted according to the totatl order and that it is a permutation of the input.
* I also gave an example for quicksort of natural numbers.
