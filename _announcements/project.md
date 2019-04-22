---
title: Project Guidelines (due date April 22, 2019)
date: April 22, 2019
---

Since the official timing of the final examination for the course is "Monday : April 22 Afternoon" according to the SCC's timetable, I will tag the final submission at 5:00 pm on Monday, April 22. 2019. For questions, clarifications and comments, please comment at the corresponding [issue](https://github.com/siddhartha-gadgil/LTS2019/issues/49).

## Goals

The goals of the project are to illustrate the integration of computation and proof in Dependent Type Theory.

## Rules and Criteria

* The code must output a solution together with a proof that it is correct.
  - It should be transparent from the output type that it proves the correct result, i.e. the evidence should not be c a complicated type that is not clearly correct.
  - if complex types help for internal computation it is a good idea to introduce them, but they should be translated to simpler ones for both input and output.
* Only valid input should be accepted, i.e., evidence for any conditions that need to be satisfied should be arguments.
  - if the evidence is hard to supply, also write helpers making it easy to generate such evidence. For example, if you need that an input is prime, there should be a complementary function to easily prove `7` is a prime.
* Credit is given both for useful algorithms and non-trivial proofs of correctness.
* Document the code.
* Give examples, typically in different files.
* Proof should be usable as arguments to other functions, e.g. a proof that a number is even should be usable in conjunction with a function requiring an even number.
  - the best projects will in fact have a tree where several pieces of evidence that are results of functions are used by other functions that need these as conditions.

## Final Submission guidelines.
* By the final submission, I expect complete code
  - no missing definitions
  - functions total, with the only exception for components of an interpreter (as interpreters cannot be total).
  - achieving the guidelines, i.e. accepting only valid input and giving output including proofs that the output satisfies all claimed properties.
* Only pull requests that pass the tests are merged.
* Please update reports along the same lines as the midterm submission.
