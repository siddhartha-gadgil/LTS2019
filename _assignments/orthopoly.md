---
title: Orthogonal polynomials and functions
date: January 22, 2018
---

Let $V$ be the vector space
$$V = \{f: [-1, 1] \to \mathbb{R} \vert \text{ $f$ is continuous}\},$$
with inner product given by
$$\langle f, g\rangle = \frac{1}{2}\int\limits_{-1}^1 f(t)g(t)dt.$$

1. Show that polynomials $x^n$ and $x^m$ (as elements of $V$) are orthogonal if and only if $n-m$ is odd.
2. Show that $f(x) = 1$ and $g(x) = \\sqrt{3}x$ form an orthonormal basis for the subspace $L \\subset V$ consisting of linear functions (you may use the fact that the constant function $1$ and the function $x$ form a basis for the space $L$).
3. Find the linear function $h(x) = ax + b$ that minimizes $$\int\limits_{-1}^1 (e^t - (at+b))^2 dt.$$
4. Find an orthonormal basis for the subspace $Q \\subset V$ consisting of polynomials of degree at most $2$.
5. Let $S$ be the subspace of $V$ consisting of _symmetric_ continuous functions, i.e., functions $f$ such that $f(-x) = f(x)$ for all $x \\in [-1, 1]$. Let $g\in V$ be an  _anti-symmetric_ function, i.e., $g(-x) = -g(x)$ for all $x \\in [-1, 1]$. Show that $\\forall f\\in S$, $$\langle f, g \rangle = 0$$.
6. For a function $f \\in V$, let $\\hat{f}$ be given by $\\hat{f}(x) = \\frac{f(x) + f(-x)}{2}$. Show that $f - \\hat{f}$ is anti-symmetric, and deduce that $\\hat{f}$ is the __orthogonal projection__ onto $S$ of $f$.
