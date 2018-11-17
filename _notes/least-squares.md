---
title: Least-Squares fitting
date: 2017-05-03
---

### The Optimization problem

Consider a collection of points in the plane, or more generally in $R^n$. In many cases, we want to find the line that is closest to this collection of points - or more generally the plane, or affine space of a fixed dimension. Two common reasons for this are:

* the points represent values of a function, and we want to approximate this by a linear function $y = mx + c"
* the points are data in some high-dimensional space - say many numbers associated to countries - and we want to capture variation in as few dimensions as is reasonable.

In both cases, we should minimize some distance, which it is best to take as the sum of squares of individual distances from a line or plane. But the correct individual distances are different - in the first case they are the vertical distances, and in the other they are the least distances to the plane.

#### The Regression problem

This is the easier problem - we want to find the _best_ linear function $y = mx+ c$. If the points are $(x_i, y_i)$, the error is the function $E(m, c) = \sigma_i (y_i - (mx_i + c))^2$. So we have to minimize a function of two variables $m$ and $c$. We can do this with the first derivative test from calculus - fortunately this has a unique solution. 

#### Best line in space

Next, suppose we want to find the line that minimizes distance. We can again wirte this as minimizing a function - though it is a nice bit of linear algebra to figure out which function. We then apply the first derivative test - which tells us that we should compute an eigenvalue. But the solution is not unique. In this case, we typically just compare the values at solutions, but this illustrates why we may need second derivative tests.
