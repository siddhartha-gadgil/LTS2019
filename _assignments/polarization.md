---
title: Norms and Inner products
date: 2018-01-12
---

In this exercise, we explore further the relation between norms and inner-products. Let $V$ be a vector space over $\\mathbb{R}$.

We shall see that:

* We can associate to each inner product $\\langle\\cdot, \\cdot \\rangle$ on $V$ a norm $\\Vert\\cdot\\Vert$ on $V$.
* Such a norm satisfies some useful properties which we take as the _definition_ of a norm on $V$.
* A norm derived from an inner-product satisfies an additional property called _parallelogram law_.
* Given the norm on $V$ associated to an inner-product, we can recover the inner-product using _polarization_.
* However, not all norms are associated to inner-products.

### Exercises

1. Let $\\langle\\cdot, \\cdot \\rangle$ be an inner-product on $V$ and define $\\Vert x \\Vert = \\sqrt{\\langle x, x\\rangle}$ for $x \\in V$. Show that
    1. for all $x\\in V$, $\\Vert x\\Vert \\geq 0$ with equality if and only if $x = 0$,
    2. for all $x \\in V$ and $c \\in \\mathbb{R}$, $\\Vert c \\cdot x\\Vert = \\vert c \\vert \\cdot \\Vert x\\Vert$,
    3. __(triangle inequality)__ for all $x, y \\in V$, $\\Vert x + y\\Vert \\leq \\Vert x\\Vert + \\Vert y \\Vert$.

    $~$

    We take these properties to be the _definition_ of a norm, i.e., a __norm__ is a function $\\Vert\cdot\\Vert: V \\to \\mathbb{R}$ that satisfies the properties (1) - (3).

2. Let $\\langle\\cdot, \\cdot \\rangle$ be an inner-product on $V$ and define $\\Vert x \\Vert = \\sqrt{\\langle x, x\\rangle}$ for $x \\in V$. Show that for $x, y \\in V$,

    $$\Vert x + y \Vert^2 + \Vert x - y \Vert^2 = 2(\Vert x\Vert^2 + \Vert y \Vert^2).$$

    This is called the _parallelogram law_.

3. Let $V = \\mathbb{R^2}$ and define $\\Vert (x, y)\\Vert = \\vert x \\vert + \\vert y \\vert$. Show that $\\Vert\\cdot\\Vert$ satisfies the properties (1) - (3) of problem __1__ (i.e., it is a __norm__), but not the parallelogram law (and is thus not obtained from an inner product).

4. Suppose a norm $\\Vert\\cdot\\Vert$ on a vector space $V$ is of the form $\\Vert x \\Vert = \\sqrt{\\langle x, x\\rangle}$ for an inner product $\\langle\\cdot, \\cdot \\rangle$, then show that the inner product is given by

    $$\langle x, y \rangle = \frac{\Vert x + y \Vert^2 - \Vert x - y \Vert^2}{4}.$$

   This is called the _polarization identity_.


**Remark:** In fact, if a norm satisfies the parallelogram law, then the polarization identity gives an inner product (this is harder to prove than the above statements).
