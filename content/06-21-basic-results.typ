#import "main-defs.typ": *
#import "statements.typ": *

== Basic results <sec:basic-results>

Let $Lambda$ be an $R$-order in the separable $K$-algebra $A$, and suppose that
there are decompositions
$
  hat(A)_P = dsum A_i "(simple components)", quad hat(Lambda)_P = dsum Lambda_i,
$ <eq:completion-decomposition>
where $Lambda_i$ is an $hat(R)_P$-order in $A_i$. Let $K_i$ be the center of
$A_i$, and $R_i$ the integral closure of $hat(R)_P$ in $K_i$. By
@th:maximal-orders-components, the maximal $hat(R)_P$-orders in $A_i$ coincide
with the maximal $R_i$-orders in $A_i$. In particular, if $Lambda$ is a maximal
$R$-order in $A$, then #source(197)by @cor:maximal-order-completions
$hat(Lambda)_P$ is a maximal $hat(R)_P$-order in $hat(A)_P$, and so by
@th:maximal-orders-components there is a decomposition
$hat(Lambda)_P = dsum Lambda_i$, with each $Lambda_i$ a maximal $R_i$-order in
the central simple $K_i$-algebra $A_i$. We may then apply the results of
Chapter~@ch:maximal-orders-over-dvr, on maximal orders in central simple
algebras over complete fields, to the orders $Lambda_i$.

Conversely, if the order $hat(Lambda)_P$ is known to have a decomposition as in
@eq:completion-decomposition for each $P$, and if each $Lambda_i$ is a maximal
order in $A_i$, then we may conclude from @th:maximal-orders-components that
$Lambda$ is necessarily a maximal order in $A$. As an illustration of these
remarks, we prove a number of basic results.

#theorem(major: true)[
  Let $M$ be a full $R$-lattice in $A$. Then $O_l (M)$ is a maximal $R$-order in
  $A$ if and only if $O_r (M)$ is a maximal $R$-order in $A$.
] <th:global-left-right-orders-maximal>

#proof[
  We know that $hat(R)_P$ is $R$-flat, by @cor:completion-flat or
  Exercise~@exc:dedekind-completion-flat. As in the proof of
  @eq:right-order-local, it follows that
  $
    O_r (hat(M)_P) = hat(R)_P times.o_R O_r (M),
  $ <eq:right-order-completion>
  and likewise for left orders. Now suppose that $Lambda = O_l (M)$ is maximal,
  and let $Gamma = O_r (M)$. Keeping the notation of
  @eq:completion-decomposition, there is also a decomposition
  $hat(M)_P = dsum M_i$, where $M_i$ is a full $hat(R)_P$-lattice in $A_i$, and
  where $Lambda_i = O_l (M_i)$. But then there is a decomposition
  $
    hat(Gamma) = dsum Gamma_i, quad "where" quad Gamma_i = O_r (M_i).
  $
  Since $Lambda$ is maximal, so is each $Lambda_i$, whence so is each $Gamma_i$
  by @th:left-right-orders-maximal. Therefore $Gamma$ is maximal, by the remarks
  preceding the theorem, and the proof is complete.
]

#theorem(major: true)[
  Maximal orders are left and right hereditary.
] <th:global-maximal-hereditary>

#proof[
  Let $Lambda$ be a maximal $R$-order in $A$, and use the notation of
  @eq:completion-decomposition. Each $Lambda_i$ is hereditary by
  @th:complete-local-maximal-orders, whence $hat(Lambda)_P$ is hereditary for
  each $P$. Thus $Lambda$ is itself hereditary, by @cor:hereditary-local and
  @th:dimension-completion.
]

#corollary[
  Let $Lambda$ be a maximal order. Then every left $Lambda$-lattice $M$ is
  $Lambda$-projective. Further, $M$ is indecomposable if and only if $K M$ is a
  simple $A$-module.
] <cor:global-lattices-projective>

#proof[
  Since $Lambda$ is hereditary, $M$ is projective by
  @cor:hereditary-lattices-projective. If $M$ decomposes, so does $K M$.
  Conversely, let $W$ be any $A$-submodule of $K M$, and set $N = M inter W$.
  Then $N$ is a $Lambda$-submodule of $M$, and by @th:pure-sublattices the
  $Lambda$-module $M slash N$ is an $R$-lattice. Hence $M slash N$ is
  $Lambda$-projective, and so the $Lambda$-exact sequence
  $
    0 -> N -> M -> M slash N -> 0
  $
  #source(198)is split. This gives a decomposition of $M$, unless $W = 0$ or
  $W = K M$, which completes the proof.
]

We are now ready to determine _all_ maximal $R$-orders in $A$. We have seen that
it suffices to handle the case of central simple algebras. We prove

#theorem(major: true)[
  Let $A = Hom_D (V, V)$ be a simple algebra, where $V$ is a right vector space
  of dimension $r$ over the skewfield $D$ with center $K$. Let $Delta$ be some
  fixed maximal $R$-order in $D$, and let $M$ be any full right $Delta$-lattice
  in $V$. Then $Hom_Delta (M, M)$ is a maximal $R$-order in $A$. If $Lambda'$ is
  any maximal $R$-order in $A$, then there exists a full right $Delta$-lattice
  $N$ in $V$ such that $Lambda' = Hom_Delta (N, N)$.
] <th:global-maximal-orders-simple>

#proof[
  Letting $Lambda = Hom_Delta (M, M)$, we have
  $
    Lambda_P = R_P times.o_R Lambda = Hom_(Delta_P) (M_P, M_P)
  $
  for each $P$. By @th:local-hereditary-principal every right ideal of $Delta_P$
  is principal, whence $M_P$ is $Delta_P$-free. Hence by
  @th:matrix-maximal-order $Lambda_P$ is a maximal $R_P$-order. This holds for
  each $P$, and so $Lambda$ is maximal by @cor:maximal-order-local.

  Now let $Lambda'$ be any maximal $R$-order in $A$. Since $Lambda$ and
  $Lambda'$ are a pair of full $R$-lattices in $A$, we have
  $Lambda'_P = Lambda_P$ a.e., say except at $P_1, dots, P_n$. By
  @th:local-hereditary-principal, for each $P$ there exists an element
  $u_P in u(A)$ such that $Lambda'_P = u_P Lambda_P u_P^(-1)$, and we may take
  $u_P = 1$ for $P != P_1, dots, P_n$. For each $P$, set $X(P) = u_P M_P$; then
  we have
  $
    Lambda'_P = Hom_(Delta_P) (X(P), X(P)).
  $
  If we define $N = inter.big_P X(P)$, then by @th:lattice-from-local-data $N$
  is a full right $Delta$-lattice in $V$, such that $N_P = X(P)$ for all $P$.
  But then $Lambda'$ and $Hom_Delta (N, N)$ are a pair of full $R$-lattices in
  $A$, with the same localizations for each $P$. Therefore
  $Lambda' = Hom_Delta (N, N)$ by Exercise~@exc:submodules-equal-locally, and
  the theorem is proved.
]

#corollary[
  Keeping the above notation, every maximal order in $A$ is Morita equivalent to
  $Delta$.
] <cor:global-maximal-morita>

#proof[
  Every maximal order $Lambda$ in $A$ is of the form
  $Lambda = Hom_Delta (M, M)$, where $M$ is some full right $Delta$-lattice in
  $V$. Since $Delta$ is hereditary, it is clear that $M$ is a finitely generated
  projective $Delta$-module. We wish to show that $M$ is a progenerator for the
  category $cal(M)_Delta$, and so we must verify that $Hom_Delta (M, dot)$ is a
  faithful functor. But for each $Delta$-module $L$, we know that
  $
    {Hom_Delta (M, L)}_P tilde.equiv Hom_(Delta_P) (M_P, L_P)
  $
  for each $P$. Since $M_P$ is $Delta_P$-free by
  Exercise~@exc:skewfield-order-lattices-free, it follows from
  §~@sec:progenerators that $Hom_(Delta_P) (M_P, dot)$ is a faithful functor.
  Therefore $Hom_Delta (M, dot)$ is also faithful, #source(199)and so we have
  proved that $M_Delta$ is a progenerator for $cal(M)_Delta$. Hence $Lambda$ and
  $Delta$ are Morita equivalent, by @cor:progenerator-morita-equivalence, and
  the result is established.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $Lambda$ be a maximal $R$-order in a separable $K$-algebra $A$, and let
  $M$ be any left $Lambda$-lattice. Show that the endomorphism ring
  $End_Lambda M$ is a maximal $R$-order in the separable $K$-algebra
  $End_A K M$. #hint[@exc:endomorphism-ring-maximal][It suffices to prove the
    result when $A$ is a central simple $K$-algebra, and where $R$ is a discrete
    valuation ring. Set $Gamma = End_Lambda M$, $B = End_A K M$, and let $V$ be
    a simple left $A$-module. Then $D = End_A V$ is the skewfield part of $A$.
    We have $K M tilde.equiv V^((t))$ for some $t$, whence
    $B tilde.equiv End_A V^((t)) tilde.equiv M_t (D)$. Thus $B$ is also a
    central simple $K$-algebra.

    Now choose a left $Lambda$-lattice $L$ in $V$ such that $K L = V$. Then
    $K M tilde.equiv (K L)^((t))$, whence $M tilde.equiv L^((t))$ by
    @th:separable-maximal-principal. Therefore
    $
      Gamma = End_Lambda M tilde.equiv End_Lambda L^((t))
      tilde.equiv M_t (Delta),
    $
    where $Delta = End_Lambda L$ is a maximal $R$-order in $D$. Hence $Gamma$ is
    a maximal $R$-order in $B$, as claimed.]
  <hint:endomorphism-ring-maximal>
] <exc:endomorphism-ring-maximal>
