---
author: Nabarun Deka
layout : report
---

### 1. Quicksort function
I created a function (**partitionVect**) that accepts a pivot and a vector and partitions the vector into two vectors according to whether the elements are smaller than or larger than the pivot, and returns the lengths of the parts as well as a proof that the sum of their lengths is equal to the length of the original vector.

### 2. Mergesort
Shafil had written an incomplete code that had a merge function to merge to sorted vectors into one sorted vector. I completed the code by creating a mergesort function. The work I did for this is :
<ul>
  <li> I created two functions that partition a Vector into two parts, the parts being equal if the length of the vector is even (**halfVectEven**), and the parts being unequal if the length of the vector is odd (**halfVectOdd**).
  <li>  I created a mergesort function that splits cases on whether the length of the Vector is Even or Odd, partitions it by the two functions I created earlier, and then applies mergesort recursively to both the parts.
</ul>

This mergesort function was not total however, because the **Vecttake** function that Shafil defined was not total. So I made it total by adding a condition that the length of the Vector that we take is LTE the length of the original Vector. To make the rest of the auxiliary functions total, I had to prove a lot of lemmas and Theorems (eg : **nLTESn**,**halfnLTEn**, etc.). However, I was unable to make the proof that if (a = b), then (a is LTE b) total.

I also started working on proving that the result of the mergesort function is sorted. For this, I thought of the following strategy :
<ul>
  <li> First, prove that the merge (**merge1**) function returns a sorted Vector. For this, I proved the auxiliary theorem that if I have a sorted Vector, v, and an element, x, which is LTE the first element of v, then the vector (x :: v) is also sorted.
  <li> Use the auxiliary theorem to construct a recursive prove that merge1 returns a sorted Vector.
  <li> Use this to Prove that mergesort returns a sorted Vector.
</ul>
