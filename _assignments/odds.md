---
title: Odds and Evens
date: 24 Jan 2019
---

All problems should be solved in an `Idris` file which should be in a folder including the files `Intro.idr` and `Evens.idr` from the course. If your user name is _myusername@iisc.ac.in_, begin the idris file with the following.

```idris
module Myusername.Odds

import Evens

import Intro

```

1. Define an inductive type family `IsOdd : Nat -> Type` such that `IsOdd n` is inhabited if and only if `n` is odd.
2. Show that `$3$` is odd.
3. Show that `$2$` is not odd.
4. Show that if `n: Nat` is odd, then its successor `S n` is even.
5. Show that if `n: Nat` is even, then its successor `S n` is odd.
6. Show that every number `n : Nat` is either even or odd.
7. Show that no number `n: Nat` is both even and odd.
8. Show that if `n: Nat` and `m: Nat` are odd, then `add n m` is even (here add is from the intro).
9. Show that if `n: Nat` is odd, then there exists `m: Nat` such that `n = S (double m)`.
