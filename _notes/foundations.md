---
title: "Foundations of Mathematics and Computation"
date: 2017-12-12
---

### Axiomatic foundations

Foundations of Mathematics should tell us what are true mathematical statements. The last layer of this is the most familiar, the _axioms_ that we know are true in advance. But before we use, or even state, these, we must

* Understand how we can build valid mathematical objects, and what are the ones we start with - the __language__ of mathematics.
* Which of these are __statements__ - _is `$1 + 2$` true?_ makes no sense -- __types__ of mathematical objects.
* Specify how to make a _judgement_ that one statement is true from knowing other statements are true (the __rules of deduction__).

Given these, we form a _theory_ by specifying that some statements, our axioms, are assumed to be true. We then have a meta-mathematical layer of judgements which is the collection of statements that we have judged to be true (more precisely, to have been proved).

We emphasise that this is not the only way in which foundations can be built. Indeed the foundations we consider will have a much richer kind of language (not just a larger vocabulary) and so axioms will play only a minor role - indeed in the pure Type Theoretic foundations we have no axioms.

### Foundations in general

All foundations we consider will have __rules__ giving

- a __language__  describing the objects we consider together with some information about their nature - which we will call __types__. Types are the analogue of _parts of speech_ in natural languages.
- __judgements__  we make about these objects; including judgements of types which are required in the rules for forming languages.

The rules must be clearly and unambiguously stated and straightforward to verify, including by a computer program.

### Higher languages

While natural langauges have a vocabulary that grows over time, the _parts of speech_ remain fixed. However in the higher languages we consider, we can _form_ new parts of speech - essentially the part of speech of a word/phrase may be given by a _type-phrase_. Indeed there are three levels of languages we consider, which in terms of _terms_ (analogues of words, phrases, sentences etc) and _types_ (analogues of parts of speech) are:

- __First-order__ : a fixed, often finite, set of types.
- __Higher-order__ : types can be built from other types, for example if `$A$` and `$B$` are types we can form the _function type_ `$A \to B$` (in programming languages these are often called _generics_).
- __Dependent types__ : types can be formed not just from types but also terms
  - for instances vectors of a fixed length form a type;
  - indeed, types are _first-class_, i.e., we cna have functions (some of whose) arguments are types and functions whose results are types (or both).

We shall see how to build such a type theory, and how it also forms foundations for _computation_.

### Computation

We communicate with computers using _programming languages_, which are languages in the above sense. However, with the most common style of programming, so called _imperative programming_, the program to describe a mathematical computation is very different from a mathematical description, as it is a set of instructions to output the result of the described objects.

However, _functional languages_, building on Church's model of computation, have descriptions that are much closer to mathematical descriptions. For instance, in pseudo-code we may define `factorial(n)` as
```
$factorial(n)$ := if $n = 0$ then $1$ else $n\cdot factorial(n-1)$
```
which is just as good a mathematical definition as any. Moreg generally, the only form of _looping_ or used in functional programming is recursion, and there is no (explicit) _flow of control_.

Indeed the foundations we study are to a substantial extent common for mathematics and computation, with the langauge for computation a restriction of the language used for mathematics. Code for a mathematical object is just an _effective_ description of that object, which merely means that it does not invoke axioms (including logical axioms such as the law of excluded middle). This would not be musch use if our foundations were Set Theory, as in set theory we use axioms at the drop of a hat. But in the Type Theoretic foundations we study, we use axioms only if there is a strong reason to use.

Examples such as the factorial function, or typical mathematical problems such as solving equations, give a misleadingly limited view of what we mean by computation. Since computation should include all operations that a computer needs to perform, we should include _interpreters_, i.e. a function _eval_ so that
```
eval("$factorial(n)$ := if $n = 0$ then $1$ else $n\cdot factorial(n-1)$")($7$)
```
should give us `$factorial(7)$`.

We can indeed write such interpreters, but such tasks will lead us to the deep unsolvability results of Turing and Godel.
