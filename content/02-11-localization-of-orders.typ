#import "main-defs.typ": *
#import "statements.typ": *

== Localization of orders <sec:localization-of-orders>

Here we investigate the relation between an $R$-order $Lambda$ in $A$ and its
#source(141)localizations $Lambda_P$ and completions $hat(Lambda)_P$, where $P$
ranges over the prime ideals of $R$. We keep the hypotheses of
section~@sec:existence-of-maximal-orders.

#theorem[
  Let $S$ be a multiplicatively closed subset of $R$. For each maximal $R$-order
  $Lambda$ in $A$, $S^(-1) Lambda$ is a maximal $S^(-1) R$-order in $A$.
] <th:localization-maximal-order>

#proof[
  By @exm:integrally-closed-domains[(e)] and @th:localization-noetherian, we
  know that $S^(-1) R$ is noetherian and integrally closed, since $R$ has these
  properties by hypothesis. Let $i : Lambda -> S^(-1) Lambda$ be the
  homomorphism $x -> 1 times.o x$, $x in Lambda$, defined as in
  @th:saturated-correspondence.

  Now $S^(-1) Lambda$ is an $S^(-1) R$-order in $A$; let $Gamma$ be any larger
  order in $A$, and choose a nonzero $alpha in R$ such that
  $alpha dot Gamma subset S^(-1) Lambda$. Then $Delta = i^(-1) (alpha Gamma)$ is
  an $S$-saturated submodule of $Lambda$ such that $alpha Gamma = S^(-1) Delta$.
  Since $i$ is a two-sided $Lambda$-homomorphism, $Delta$ is a two-sided
  $Lambda$-module. Then the right order $O_r (Delta)$ coincides with $Lambda$,
  since $O_r (Delta) supset Lambda$ and $Lambda$ is maximal. Hence by
  @eq:right-order-base-change we have
  $
    S^(-1) Lambda = O_r (S^(-1) Delta) = O_r (alpha Gamma) = Gamma,
  $
  which completes the proof.
]

#corollary[
  An $R$-order $Lambda$ in $A$ is maximal if and only if for each maximal ideal
  $P$ of $R$, $Lambda_P$ is a maximal $R_P$-order in $A$.
] <cor:maximal-order-local>

#proof[
  If $Lambda$ is maximal, so is each $Lambda_P$ by
  @th:localization-maximal-order. Conversely, assume that each $Lambda_P$ is
  maximal, and let $Lambda subset Gamma$, where $Gamma$ is any $R$-order in $A$.
  Then $Lambda_P subset Gamma_P$, so that $Lambda_P = Gamma_P$ for all $P$. But
  then $(Gamma slash Lambda)_P = 0$ for all $P$, whence $Gamma = Lambda$ by
  @th:local-global-zero.
]

The following material, up to @th:completion-maximal-order, can be skipped by
the reader interested only in the case where $R$ is a Dedekind domain. The above
result shows that the question of whether an $R$-order $Lambda$ is maximal is a
"local" one, and can be decided by knowing whether the localizations $Lambda_P$
are maximal orders, where $P$ ranges over the maximal ideals of $R$. Now if
$P' subset P$ are a pair of prime ideals of $R$, we have an inclusion
$Lambda_P subset Lambda_(P')$, and indeed
$
  Lambda_(P') tilde.equiv (R_P)_(P' dot R_P) times.o_(R_P) Lambda_P,
$
that is, $Lambda_(P')$ is a localization of $Lambda_P$ at the prime ideal
$P' dot R_P$ of $R_P$. Hence if $Lambda_P$ is a maximal $R_P$-order, then by
@th:localization-maximal-order, $Lambda_(P')$ is necessarily a maximal
$R_(P')$-order. Thus the hypothesis that $Lambda_P$ be a maximal order for each
_maximal_ ideal $P$ of $R$ is a rather strong one, since it implies that
$Lambda_(P')$ is a maximal $R_(P')$-order for _every_ prime ideal $P'$ of $R$.
The weakest hypothesis would be the assumption that $Lambda_(P')$ is a maximal
order for every _minimal_ prime $P'$ of $R$. (Recall that a _minimal prime_ of
$R$ is any minimal member in the set of nonzero prime ideals of $R$.)

#source(142)The following result shows that in order to decide whether $Lambda$
is maximal, it suffices to consider the ring structure of the localizations of
$Lambda$ at the minimal primes of $R$, together with the structure of $Lambda$
as an $R$-module. We recall (see page~@eq:dual-module[page]) that $Lambda$ is a
_reflexive_ $R$-module if $Lambda = Lambda^(**)$, where
$
  Lambda^* = Hom_R (Lambda, R), quad Lambda^(**) = Hom_R (Lambda^*, R).
$
We saw in @th:krull-ring that for any noetherian integrally closed domain $R$,
we have
$
  Lambda^(**) = inter.big_P Lambda_P,
$ <eq:reflexive-intersection-of-localizations>
where $P$ ranges over the minimal primes of $R$. Using this, we prove

#theorem(title: [Auslander–Goldman [@bib:Auslander1960a]])[
  An $R$-order $Lambda$ is maximal if and only if $Lambda$ is a reflexive
  $R$-module such that for each minimal prime $P$ of $R$, $Lambda_P$ is a
  maximal $R_P$-order.
] <th:auslander-goldman-maximal>

#proof[
  Obviously $Lambda subset Lambda^(**)$ since $Lambda subset Lambda_P$ for each
  $P$. By @th:krull-lattice-from-local-data, $Lambda^(**)$ is a full $R$-lattice
  in $A$. Furthermore, $Lambda^(**)$ is a ring by
  @eq:reflexive-intersection-of-localizations, since it is an intersection of
  rings. Thus $Lambda^(**)$ is an $R$-order in $A$ containing $Lambda$. If
  $Lambda$ is a maximal $R$-order, then we have $Lambda^(**) = Lambda$, and
  hence $Lambda$ is reflexive. The fact that each $Lambda_P$ is maximal has
  already been shown in @th:localization-maximal-order.

  Conversely, let $Lambda$ be reflexive, and let each $Lambda_P$ be maximal.
  Then
  $
    Lambda = Lambda^(**) = inter.big_P Lambda_P, quad P "minimal".
  $
  If $Lambda subset Gamma$, with $Gamma$ an $R$-order in $A$, then
  $Lambda_P subset Gamma_P$ for each $P$, whence $Lambda_P = Gamma_P$ for each
  $P$. Thence
  $
    Gamma subset inter.big_P Gamma_P = inter.big Lambda_P = Lambda,
  $
  so $Lambda$ is maximal. This completes the proof.
]

In applying @cor:maximal-order-local or @th:auslander-goldman-maximal, we are
faced with the problem of deciding whether the $R_P$-order $Lambda_P$ in $A$ is
maximal. The underlying ring $R_P$ is an integrally closed local noetherian
domain, with unique maximal ideal $P dot R_P$. When $R_P$ is a discrete
valuation ring, we now show that we may pass to the completion, and then
consider the problem in the complete case.

#theorem[
  Let $R$ be a discrete valuation ring#ed-note[The book states the theorem for
    an integrally closed local noetherian domain $R$. It fails in dimension 2:
    for $R = bold(Q)[x, y]$ localized at $(x, y)$ and the quaternion algebra
    $i^2 = x$, $j^2 = 1 + y$ over $bold(Q)(x, y)$, the order
    $R + R i + R j + R i j$ is maximal by @th:auslander-goldman-maximal, but
    $1 + y$ is a square in $hat(R) = bold(Q)[[x, y]]$, and $hat(Lambda)$ lies
    properly in an order with matrix units. The book applies the theorem only to
    discrete valuation rings.], $hat(R)$ its completion, and $hat(K)$ the
  quotient field of $hat(R)$. Let $Lambda$ be an $R$-order in $A$, and set
  $
    hat(Lambda) = hat(R) times.o_R Lambda, quad hat(A) = hat(K) times.o_K A,
  $
  so $hat(Lambda)$ is an $hat(R)$-order in $hat(A)$. Then $Lambda$ is a maximal
  $R$-order in $A$ if and only if $hat(Lambda)$ is a maximal $hat(R)$-order in
  $hat(A)$.
] <th:completion-maximal-order>

#proof[
  #source(143)Suppose $Lambda$ maximal, and let $hat(Lambda) subset Delta$,
  where $Delta$ is an $hat(R)$-order in $hat(A)$. Then $Gamma = A inter Delta$
  is an $R$-order in $A$ and $hat(Gamma) = Delta$, by @th:lattices-completion.
  Since $Lambda subset Gamma$, we deduce that $Lambda = Gamma$, and thus
  $hat(Lambda) = Delta$. This proves that $hat(Lambda)$ is maximal.

  Conversely, let $hat(Lambda)$ be maximal, and let $Lambda subset Gamma$ for
  some $R$-order $Gamma$ in $A$. Then $hat(Lambda) subset hat(Gamma)$, so
  $hat(Lambda) = hat(Gamma)$, and thus by @th:lattices-completion
  $Lambda = A inter hat(Lambda) = A inter hat(Gamma) = Gamma$. This completes
  the proof.
]

#corollary[
  Let $R$ be a Dedekind domain, and $Lambda$ an $R$-order in $A$. Then $Lambda$
  is a maximal order if and only if for each prime ideal $P$ of $R$, the
  $P$-adic completion $hat(Lambda)_P$ is a maximal $hat(R)_P$-order in
  $hat(A)_P$.
] <cor:maximal-order-completions>

#proof[
  This follows from @cor:maximal-order-local and @th:completion-maximal-order.
]

#heading(level: 3, numbering: none, outlined: false)[Exercise]

#exercise[
  Let $R'$ be a ring of quotients of the domain $R$, and let $M$ be an
  $R$-lattice, $X$ a full $R'$-lattice in $K M$. Show that $M inter X$ is an
  $R$-lattice in $M$ of the same $R$-rank as $M$.
] <exc:lattice-intersection-quotient-ring>
