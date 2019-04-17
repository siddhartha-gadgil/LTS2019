---
title: Languages and Limits of Mathematics and Computation
date: March 26, 2019
---

In this note we discuss what we have illustrated that we can do - parsing and interpretation, and show how this leads to results about what is impossible.

## The Setup

### Functional languges

The languages we use are functional languages, i.e., langauges where functions are first-class objects, so we can have functions of functions and so on, and where definitions can be recursive. Indeed recursion is the only form of looping we have. Idris is certainly a functional langauge, but so is the `HackyLang` that we have created.

__Note:__ We have extending `HackyLang` adding expressions for pairs - `Cons` to form pairs, `Left: Exp -> Exp` and `Right: Exp -> Exp` for projections and introduced `Null` to deal with invalid cases. We have also added a data type `Program`, which is a context with a main expression (to be though of as a function), and a `run` function that takes a program and an input expression, applies the main expression to the input and interprets in the context.

A rich type system makes programming much easier and more pleasant, but the power of a weakly/dynamically typed functional language is no less. So while we have illustrated various things with `Idris` code, we can presumaby write code in `HackyLang`. In practice it would be best to use say `Scheme` (or a subset of it) to replace both `Idris` and `HackyLang`, and it is a nice project to port this part of the course to `Scheme`.

### Parsers and their combinations

In functional langauges parsing can be very pleasant. We view parsers as functions taking an input and giving an output, or rather a `ParseResult`. The key point is we can define parsers by combinations of other parsers - _sequencing_ (i.e. `++`), _alternatives_ (i.e. `||`), _mapping_, _repetition_ and _flat-mapping_. Starting with basic parsers that just match a single character based on a predicate, we can combine mutually recursively to parse a language.

We can presumably do all this in `HackyLang`, with `ParseResult` replaced by a pair with

* first entry Boolean saying whether parse is successful
* second entry
  - if parse is successful, a pair with result and unconsumed output.
  - if parse fails, say `Null` (it can be anything).

A string can be represented by an iterated pair of characters (with characters represented by natural numbers). One can readily implement basic parsers as well as combinations. Doing this in `Scheme` is an enjoyable exercise.

### Parsers and Intepreters for and in `HackyLang`

We have written in code and illustrated in lectures

* A parsers (in Idris), `ExpressionParser`, for a language smaller but more complex that `HackyLang` (since we needed to flat-map to deal with context dependence of parsing).
* An interpreter for expressions in `HackyLang` built by recursive application of _simplification_ (__warning:__ simplification may actually complicate).
* A program in `HackyLang` that can compute the factorial function.
* Made enhancements to `HackyLang` to include pairs and a notion of running programs.
* Made a program to sum lists of natural numbers using `HackyLang`.

We hope this is enough to make all the claimed constructions below plausible.

## Theorems of Church and Turing

We sketch how diagonal arguments let us prove some fundamental results showing the limits of computation.

### A postulated language

We postulate that we have a language and associated objects that satisfy the following:

* The language has _definitions_ and _expressions_, with a collection of definitions forming a _context_. Expressions include literals, strings, $\\lambda$-definitions, function applications etc.
* We can _simplify_ an expression in a context. Iterated simplification may or may not terminate in a literal.
* We take a program to be a context and a main expression. Running this on an input expression (which we take to be a string) means applying the function to the input and repeatedly simplifying. By definition, we say running the program terminates on the input if repeated simplification gives a literal string. We view this as a _partially defined_ `run` function `run: Program -> String -> String`
* We can `quote` programs, i.e. represent them by strings.
* We have a (in general partially defined) _interpreter_ function `eval : String -> String -> String` so that if the program `P` when run with input `s` terminates with output `t`, then `eval (quote P) s = t` (by this we mean the lhs is defined and equals the rhs). We say `eval` is a _total interpreter_ if it is defined in all cases, though there is no restriction on what it outputs except for programs and terminating input.

### The results

__Theorem 1:__ A language as postulated above cannot have a total interpreter defined in itself.

__Proof:__

* Assume that we have such a total interpreter `eval`.
* Define `evil: String -> String` given by `evil s = (eval s s) + " contrariwise"`
* Let `evilProg` be the program giving this definition.
* Note that as `eval` is total, `evilProg` also terminates with all inputs, i.e. `runEvilprog s` is always defined
* Thus for any string `s`,  `eval (quote evil) s = evil s`
* Observe that
```
evil (quote evil) = (eval (quote Evil) (quote Evil)) + " contrariwise"
                    = (evil (quote evil)) + " contrariwise"
```
* The above is absurd, giving a contradiction to the existence of a total interpreter.

We can bootstrap this result to prove some fundamental results. We say that a function `f` is _computable_ if there is a program in our language that when run with input arguments to `f` outputs the result. This depends on our language, but if we can interpret another language in ours, then computability in the other language implies computability in ours.

Let `halt: String -> String -> Bool` be the function such that `halt(q)(s)` is true if and only if `q = quote P` and `P` halts when run with input `s`.

__Theorem 2:__ The function `halt` is not computable.

__Proof:__ Assume that `halt` is computable. Then we can modify the (partially defined) `eval` function to be a total interpreter, namely define

```idris
safeEval : String -> String -> String
safeEval q s = if (halt q s) then eval q s else "farewell and thanks for all the fish".
```

It follows that there is a function that grows faster than any computable function.

__Theorem 3:__ There is a function `$f: \mathbb{N} \to \mathbb{N}$` such that if `$g: \mathbb{N} \to \mathbb{N}$` is a computable function, for some `$n \in \mathbb{N}$` we have `$f(n) > g(n)$`.

__Proof:__

For a natural number `n`, consider all programs `P` of length `n` and strings `s` with length `n` so that the program `P` with input `s` terminates. Given such a `P` and `s`, let `t(P, s)` be the number of simplification steps needed when running the program `P` with input `s`. Let `f(n)` be the maximum of `t(P, s)` over all such pairs.

We see that `$f$` is as claimed. Suppose not. Then there is a computable function `$g: \mathbb{N} \to \mathbb{N}$` such that  `$f(n)\leq g(n)\ \forall n\in\mathbb{N}$`. Then it is easy to define a computable function `halt` using `$g$`, contracting Theorem 2.
