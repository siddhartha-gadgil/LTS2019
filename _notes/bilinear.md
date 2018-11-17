---
date: February 8, 2018
title: Bilinear and Quadratic forms
---

### Bilinear and Quadratic forms

* Let $V$ be a vector space over a field $k$ in which $2 \\neq 0$ (say real or complex numbers).
* A _Bilinear form_ $B(x, y)$ is a function $B : V \\times V \\to k$ which is linear in $x$ and $y$.
* We can associate to a Bilinear form $B$ a so called _quadratic form_ $Q : V \\to k$ defined by $Q(x) = B(x, x)$. Note that by definition a Quadratic form is associated to a Bilinear form.
* Given the Bilinear form $B$, we can define a __symmetric__ Bilinear form $\\bar{B}(x, y) = \\frac{B(x, y) + B(y, x)}{2}$.
* If $\\bar{Q}(x)$ is the quadratic form associated to $\\bar{B}$, then it is easy to see that $\\bar{Q} = Q$.
* Thus, every quadratic form $Q(x)$ is of the form $Q(x) = B(x, x)$ with $B$ __symmetric__.
* The symmetric Bilinear form $B$ with $Q(x) = B(x, x)$ is determined by $Q$, as can be shown by __polarization__.

### Bilinear forms and Linear operators

* Now assume that $V$ is a finite dimensional Euclidean space over $\\mathbb{R}$.
* Given a linear transformation $L: V \\to V$, we can define a Bilinear form $B(x, y) = \\langle x, L(y) \\rangle$.
* We see that __all__ Bilinear forms are of this form.

#### Theorem
Let $B(x, y)$ be a Bilinear form on $V$. Then there exists a unique linear transformation $L$ such that $B(x, y) = \\langle x, L(y) \\rangle$ for all $x, y \\in V$.

#### Proof
* Fix a Bilinear form $B(x, y)$ on $V$.
* For a fixed vector $y \\in V$, we can define a linear functional $\\theta\_y: V \\to \\mathbb{R}$ by $\\theta\_y(x) = B(x, y)$.
* As in the note on duality, there is a unique vector $z\_y$ such that for all $x \\in V$, $\\theta\_y(x) = \\langle x, z\_y\\rangle$.
* We define $L: V \\to V$ by $L(y) = z\_y$. It is easy to see that this is a linear transformation.
* Thus, $B(x, y) = \\theta\_y(x) = \\langle x, z\_y\\rangle = \\langle x, L(y) \\rangle$ as required.

A linear transformation from a vector space $V$ to itself is also called a _linear operator_ on $V$.


### Adjoints and self-adjoint operators.
* Let $L: V\\to V$ be a linear transformation. Let $B(x, y) = \\langle x, L(y)\\rangle$ as before.
* Then $(x, y) \\mapsto B(y, x) = \\langle y, L(x)\\rangle$ is also a Bilinear form.
* Hence, by the above theorem, there exists a unique linear transformation $L^\*$ such that $B(y, x) = \\langle x, L^\*(y)\\rangle$.
* Using symmetry of the inner product, we can thus write $\\langle x, L(y)\\rangle = \\langle L^\*(x), y\\rangle$ for all $x, y\\in V$.
* $L^\*$ is called the _adjoint_ of $L$. We say $L$ is _self-adjoint_ if $L = L^\*$.
* As $B(x, y) = \\langle x, L(y)\\rangle$ and $B(y, x) = \\langle x, L^\*(y)$ for all $x, y\\in V$, it follows that $B$ is symmetric if and only if $L= L^\*$, i.e. $L$ is self-adjoint.
* In particular, any quadratic form $Q(x)$ is given by $Q(x) = \\langle x, L(x)\\rangle$ for a unique self-adjoint linear transformation $L: V \\to V$.

### Matrices
* Let $v\_1$, $v\_2$, $\\dots$, $v\_n$ be an orthonormal basis for $V$ and $L: V \\to V$ a linear transformation.
* Then the matrix $A$ of $L$ with respect to $v\_1$, $v\_2$, $\\dots$, $v\_n$ has entries $a\_{ij} = \\langle v\_i, L(v\_j)\\rangle$.
    - By definition, the entries $a\_{ij}$ of $A$ are given by $L(v\_j) = \\sum\\limits\_{i=1}^n a\_{ij}v\_i$, i.e., the coefficients of $L(v\_j)$ expressed in terms of the basis elements $v\_i$.
    - We take the inner product with $v\_{i\_0}$, for fixed $i\_0$, to get $\\langle v\_{i_0}, L(v\_j)\\rangle = \\sum\\limits\_{i=1}^n a\_{ij}\\langle v\_{i\_0}, v\_i\\rangle = a\_{i\_0j}$ as $v\_1$, $v\_2$, $\\dots$, $v\_n$ is orthonormal.
* It follows that $a\_{ij} = B(x\_i, x\_j)$.
* As the adjoint $L^\*$ corresponds to $(x, y) \\mapsto B(y, x) = \\langle y, L(x)\\rangle$, it follows that the $(i, j)$-entry of the matrix of $L^\*$ is $B(x\_j, x\_i)$, i.e., the matrix of $L^\*$ is the __transpose__ $A^T$.
* In particular, self-adjoint operators are those whose matrices are __symmetric__.
