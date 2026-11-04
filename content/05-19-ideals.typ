#import "main-defs.typ": *
#import "statements.typ": *

== Ideals <sec:ideals-local>

Throughout this section, let $Lambda$ be a maximal $R$-order in a central simple
$K$-algebra $A$, where $R$ is a discrete valuation ring, not necessarily
complete. We shall study here the factorization properties of one-sided ideals
of $Lambda$, and begin with a number of definitions.

For a pair of full $R$-lattices $M, N$ in $A$, define their product $M dot N$ in
the usual way, as the full $R$-lattice consisting of all finite sums
$sum m_i n_i$, $m_i in M$, $n_i in N$. Call $M$ a _normal ideal_#idx(
  "normal ideal",
)#idx("ideal", "normal") in $A$ if both $O_l (M)$ and $O_r (M)$ are maximal
orders. By @th:left-right-orders-maximal and @rem:local-capacity[(ii)], if one
of these orders is maximal, then so is the other. Call these orders
_similar_;#idx("similar orders") by @th:local-hereditary-principal, they are
necessarily conjugate in $A$. The normal ideal $M$ is _two-sided_ if
$O_l (M) = O_r (M)$. In the special case where #source(191)$A = K$, the normal
ideals are precisely the fractional $R$-ideals of $K$ (see
§~@ss:ideal-theory-modules), and are of course two-sided.

An _integral ideal_#idx("integral ideal")#idx("ideal", "integral") in $A$ is a
normal ideal $M$ such that $M subset O_l (M)$.

#theorem[
  If $M$ is a normal ideal such that $M subset O_l (M)$, then also
  $M subset O_r (M)$, and conversely.
] <th:integral-ideal-both-sides>

#proof[
  Let $Lambda = O_l (M)$, so $M$ is a left ideal of $Lambda$. Hence
  $M = Lambda x$ for some $x in u(A)$, and clearly
  $
    O_r (M) = O_r (Lambda x) = x^(-1) Lambda x.
  $ <eq:right-order-of-principal>
  Since $x in Lambda$, we have $x Lambda subset Lambda$, whence
  $
    M = x^(-1) dot x Lambda dot x subset x^(-1) Lambda x = O_r (M).
  $
  This completes the proof.
]

If $M$ is a two-sided normal ideal with $Lambda = O_l (M) = O_r (M)$, we shall
also refer to $M$ as a _two-sided $Lambda$-ideal_ in $A$.

#theorem[
  The set of two-sided $Lambda$-ideals in $A$ is an infinite cyclic group with
  generator $rad Lambda$ and identity element $Lambda$, relative to the usual
  multiplication of lattices.
] <th:two-sided-ideals-cyclic>

#proof[
  Let $frak(P) = rad Lambda$, so by @th:local-maximal-two-sided-ideals every
  nonzero two-sided ideal of $Lambda$ is a power of $frak(P)$. In particular we
  have $pi Lambda = frak(P)^m$ for some $m$. Define
  $frak(P)^(-1) = pi^(-1) frak(P)^(m-1)$, a two-sided $Lambda$-ideal in $A$.
  Then $frak(P) dot frak(P)^(-1) = frak(P)^(-1) dot frak(P) = Lambda$. If $X$ is
  any two-sided $Lambda$-ideal in $A$, then for some $s$, $pi^s X$ is a
  two-sided ideal in $Lambda$, and so $X = pi^(-s) frak(P)^k$ for some $k$. Thus
  $X$ is a power of $frak(P)$, and $X^(-1) = pi^s (frak(P)^(-1))^k$. This
  completes the proof.
]

An integral ideal $M$ will be called a _maximal integral ideal_#idx(
  "maximal integral ideal",
)#idx("ideal", "maximal integral") if $M$ is a maximal left ideal in $O_l (M)$.
(Some authors refer to such ideals as _indecomposable_#idx(
  "indecomposable ideal",
) ideals, but we shall not use this terminology here.)

#theorem[
  If the normal ideal $M$ is a maximal left ideal of $O_l (M)$, then $M$ is a
  maximal right ideal in $O_r (M)$, and conversely.
] <th:maximal-integral-both-sides>

#proof[
  Let $M = Lambda x$ be a maximal left ideal in $Lambda$, where
  $Lambda = O_l (M)$. By @eq:right-order-of-principal,
  $O_r (M) = x^(-1) Lambda x = Lambda'$, say. By @th:local-maximal-right-ideals,
  $x Lambda$ is a maximal right ideal in $Lambda$. Therefore
  $x^(-1) dot x Lambda dot x$ is a maximal right ideal in $x^(-1) Lambda x$.
  This proves that $M$ is a maximal right ideal in $Lambda'$, as claimed. We
  also remark for future use that conjugation by $x^(-1)$ yields an isomorphism
  of $R$-modules:
  #source(192)
  $
    Lambda / (Lambda x) tilde.equiv (x^(-1) Lambda x) /
    (x^(-1) dot Lambda x dot x) = (Lambda') / (Lambda' x).
  $ <eq:maximal-ideal-conjugation>
]

We have thus proved that the property of an integral ideal being maximal does
not depend on whether we consider it as a left ideal in its left order, or a
right ideal in its right order. We may also conclude that _all_ maximal integral
ideals in $A$ are mutually conjugate, since each pair of maximal orders are
conjugate, and for a given maximal order $Lambda$, any two maximal left ideals
of $Lambda$ are conjugate by @th:local-maximal-right-ideals.

Let $M, N$ be any pair of full $R$-lattices in $A$. We say that their product
$M dot N$ is _proper_#idx("proper product") if $O_r (M) = O_l (N)$. Likewise, a
product $M_1 dot M_2 dots.c M_k$ is _proper_ if $O_r (M_i) = O_l (M_(i+1))$,
$1 <= i <= k - 1$.

#theorem[
  Let $M$ be a proper left ideal of the maximal order $Lambda$, such that the
  $Lambda$-module $Lambda slash M$ has a composition series of length $k$. Then
  $M$ is expressible as a proper product of $k$ maximal integral ideals
  $
    M = M_1 M_2 dots.c M_k,
  $
  with
  $
    O_l (M) = O_l (M_1), quad O_r (M) = O_r (M_k).
  $
] <th:proper-product-factorization>

#proof[
  Use induction on $k$, the result being trivial when $k = 1$. Assume that
  $k > 1$, and that the theorem is known for the case $k - 1$. We can choose a
  maximal left ideal $Lambda x$ of $Lambda$ such that
  $M subset Lambda x subset Lambda$, and then $Lambda x slash M$ has composition
  length $k - 1$. Let $Lambda' = x^(-1) Lambda x$; then $Lambda'$ is a maximal
  order, and there is a bijection $W -> x^(-1) W$ between the set of
  $Lambda$-modules $W$ and the set of $Lambda'$-modules $x^(-1) W$. Therefore
  $x^(-1) M$ is a left ideal of $Lambda'$, and $x^(-1) Lambda x slash x^(-1) M$
  has composition length $k - 1$ as left $Lambda'$-module. It follows from the
  induction hypothesis that we may write $x^(-1) M = M_2 dots.c M_k$, a proper
  product of maximal integral ideals, with
  $
    O_l (M_2) = O_l (x^(-1) M) = x^(-1) Lambda x = Lambda'.
  $
  If we set $M_1 = Lambda x$, then $M_1$ is a maximal integral ideal such that
  $O_r (M_1) = Lambda'$. Therefore the factorization
  $
    M = Lambda x dot x^(-1) M = M_1 M_2 dots.c M_k
  $
  expresses $M$ as a proper product of maximal integral ideals. Once such a
  factorization is known, then there are obvious inclusions
  $
    O_l (M) supset O_l (M_1), quad O_r (M) supset O_r (M_k).
  $
  Since all of these orders are maximal, equality must hold. This completes the
  proof.
]

#corollary[
  #source(193)Let $rad Lambda$ have capacity $t$, that is,
  $
    Lambda slash rad Lambda tilde.equiv M_t (S)
  $
  for some skewfield $S$. Then $rad Lambda$ is expressible as a proper product
  of $t$ maximal integral ideals.
] <cor:radical-proper-product>

#proof[
  $M_t (S)$ is a direct sum of $t$ simple left $Lambda$-modules, and hence
  $Lambda slash rad Lambda$ has composition length $t$.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Show that in a proper product of maximal integral ideals, the factors need not
  commute with one another. #hint[@exc:maximal-integral-noncommuting][Suppose
    that $M_1 dot M_2 = M_2 dot M_1$, where $M_1, M_2$ are maximal integral
    ideals. If the algebra $A$ is $M_n (D)$, where $n > 1$, then $M_1$ is _not_
    a two-sided $O_l (M_1)$-ideal. Therefore
    $
      O_l (M_1 M_2) = O_l (M_1), quad
      O_l (M_2 M_1) = O_l (M_2) = O_r (M_1) != O_l (M_1).
    $] <hint:maximal-integral-noncommuting>
] <exc:maximal-integral-noncommuting>

#exercise[
  Show that in some cases an integral ideal may be expressed in more than one
  way as a proper product of maximal integral ideals.
  #hint[@exc:non-unique-factorization][Let $A = M_2 (K)$, $Lambda = M_2 (R)$,
    $x_1 = mat(1, 0; 0, pi)$, $x_2 = mat(pi, 0; 0, 1)$, where $pi$ is a prime
    element of $R$. Then $x_1, x_2$ commute, and
    $
      pi Lambda = Lambda x_1 dot x_1^(-1) (Lambda x_2) x_1
      = Lambda x_2 dot x_2^(-1) (Lambda x_1) x_2
    $
    gives two different factorizations of $pi Lambda$.]
  <hint:non-unique-factorization>
] <exc:non-unique-factorization>
