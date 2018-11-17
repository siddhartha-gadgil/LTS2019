---
title: Duality and Inner Products
date: Feb 7, 2018
---

#### Dual space

* Let $V$ be a vector space over a field $k$.
* A _linear functional_ $\\lambda$ on $V$ is a linear transformation $\\lambda: V \\to k$.
* Linear functionals form a vector space, called the _dual space_ $V^\*$ of $V$.

#### Duality in Euclidean spaces

* Assume now that $V$ is a finite-dimensional vector space over $\\mathbb{R}$ equipped with an inner product $\\langle\\cdot,\\cdot\\rangle$.
* Let $w\\in V$ be a fixed vector. Then we can define a linear functional $\\lambda\_w: V \\to\\mathbb{R}$ by
$\\lambda\_w(v) = \\langle v, w \\rangle$ for an arbitrary vector $v\\in V$.
* We thus obtain a linear map $ev: V \\to V^\*$ given by $ev: w \\mapsto \\lambda\_w$.
* This is injective: if $w \\neq 0$, $\\lambda\_w = \\langle w, w \\rangle >0$ and so $\\lambda\_w \\neq 0$.

In fact, the linear transformations $\\lambda\_w$ are __all__ the linear transformations, i.e., the map $ev: V \\to V^\*$ is bijective, as we see from the following theorem.

**Theorem:** Let $\\alpha: V \\to \\mathbb{R}$ be any linear functional. Then there exists a vector $w \\in V$ such that $\\alpha = \\lambda\_w$, i.e., for all $v\\in V$, $\\alpha(v) = \\lambda\_w(v)$.

**Proof:**

* Fix a linear functional $\\alpha: V \\to \\mathbb{R}$.
* We construct below a vector $w$ with $\\alpha = \\lambda\_w$.
* Recall that $V$ has an orthonormal basis $v\_1$, $v\_2$, $\\dots$, $v\_n$.
* Let $w = \\sum\\limits\_{i=1}^n \\alpha(v\_i) v\_i $.
* For $1\\leq j \\leq n$, we  see that
    - $\\lambda\_w(v\_j) = \\langle v\_j, w \\rangle$ by definition.
    - $\\langle v\_j, w \\rangle = \\sum\\limits\_{i=1}^n \\alpha(v\_i) \\langle v\_j, v\_i \\rangle = \\alpha(v\_j)$, as $w = \\sum\\limits\_{i=1}^n \\alpha(v\_i) v\_i $ and $\\langle v\_j, v\_i \\rangle = \\delta\_{ji}$.
    - Thus, $\\lambda\_w(v\_j) = \\alpha(v\_j)$.
* As linear transformations are determined by their values on basis elements, it follows that $\\alpha = \\lambda\_w$, completing the proof of the theorem.
* As $\\alpha$ was arbitrary and $\\alpha = \\lambda_w = ev(w)$ (the second equality is by definition of $ev$), it follows that $ev$ is surjective, hence bijective.
