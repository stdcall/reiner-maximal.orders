#import "main-defs.typ": *
#import "statements.typ": *

= Maximal Orders over Dedekind Domains <ch:maximal-orders-over-dedekind-domains>

#source(196)Throughout this chapter, $R$ denotes a Dedekind domain with quotient
field $K$, $R != K$, and $P$ ranges over the maximal ideals of $R$. Let $R_P$ be
the localization of $R$ at $P$, and $hat(R)_P$ the $P$-adic completion of $R$.
Let $hat(K)_P$ be the quotient field of $hat(R)_P$. For $Lambda$ any $R$-order
in the separable $K$-algebra $A$, and $M$ any $Lambda$-module, set
$
  hat(Lambda)_P = hat(R)_P times.o_R Lambda, quad
  hat(M)_P = hat(R)_P times.o_R M, quad
  hat(A)_P = hat(K)_P times.o_K A.
$
Then $hat(Lambda)_P$ is an $hat(R)_P$-order in $hat(A)_P$, and $hat(M)_P$ is a
$hat(Lambda)_P$-module. It follows from Exercise~@exc:separable-base-change that
$hat(A)_P$ is a separable $hat(K)_P$-algebra.

In this chapter we shall generalize the theorems obtained in
Chapters~@ch:maximal-orders-in-skewfields and~@ch:maximal-orders-over-dvr. There
are two ways of accomplishing this. In the first approach, followed in
§§~@sec:basic-results–@sec:ideal-theory, we use the local results from
Chapter~@ch:maximal-orders-over-dvr, together with the techniques of
§~@ss:completions, to obtain global results. The second approach, given in
§~@sec:alternate-global-ideal-theory, is independent of the first, and also
yields the basic theorems for the global case. In this second method, we give
some straightforward generalizations of some of the familiar proofs in algebraic
number theory. Indeed, this same dichotomy already occurs in algebraic number
theory. One can develop the ideal theory of Dedekind domains either from the
standpoint of valuation theory (first approach), or by manipulations with the
ideals themselves (second approach). Just as in algebraic number theory,
however, we cannot in the long run avoid the use of $P$-adic completions. Many
of the deeper results depend on the interrelations between the global and local
theories. Indeed, we have already seen in @th:local-different that when $R$ is a
discrete valuation ring, we may calculate the different
$frak(D)(Lambda slash R)$ by passing to completions.
