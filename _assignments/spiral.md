---
title: Dynamics with complex Eigenvalues
date: 2018-04-16
---

Please __do not__ submit this assignment. This is to only help with understanding the material on ODEs. It is __not__ a model for final examination questions.

Let $A : \\mathbb{R}^2 \\to \\mathbb{R}^2$ be a linear transformation. We can also regard this as a linear transformation $A : \\mathbb{C}^2 \\to \\mathbb{C}^2$.

* For what values of $tr(A)$ and $det(A)$ does $A$ have eigenvalues $\\alpha \\pm i\\beta$ for $\\alpha, \\beta \\in\\mathbb{R}$ with $\\beta\\neq 0$?

Assume henceforth that $A$ has complex eigenvalues $\\alpha \\pm i\\beta$ for $\\alpha, \\beta \\in\\mathbb{R}$ with $\\beta\\neq 0$.

* Let $\\lambda = \\alpha + i\\beta$ and let $v\\in\\mathbb{C}^2$ be an eigenvector of $A$ with $Av = \\lambda v$. Show that its (component-wise) complex conjugate $\\bar{v}$ is also an eignevector.
* Let $w_1 = (v + \\bar{v})/2$ and $w_2 = (v - \\bar{v})/2i$. Show that $w_1, w_2 \\in\\mathbb{R}^2\\subset{\\mathbb{C}}^2$ and $w_1$, $w_2$ form a basis of $\\mathbb{R}^2$ (as a __real__ vector space).
* Find the matrix of $A$ with respect to the basis $w_1$, $w_2$.
* Recall that $\\mathbb{C}$ is a __real__ vector space with basis $1, i$. Let $P: \\mathbb{R}^2 \\to \\mathbb{C}$ be the (invertible) linear transformation such that $P(w_1) = 1$ and $P(w_2) = i$. Let $B = P\\circ A \\circ P^{-1}$.
Show that $B(z) = \\lambda z$ for all $z \\in \\mathbb{C}$.
