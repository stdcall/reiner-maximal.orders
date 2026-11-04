#import "main-defs.typ": *
#import "statements.typ": *

== Ideal theory <sec:ideal-theory>

In this section we shall develop the theory of one-sided and two-sided ideals in
maximal orders over a Dedekind ring $R$ with quotient field $K$, by using the
results of §§~@sec:maximal-orders-local-case, @sec:ideals-local for the local
case. Let $P, Q, dots$ denote prime ideals of $R$, _always assumed to be
nonzero_. To begin with, let $Lambda$ be any $R$-order in a separable
$K$-algebra $A$.

A _prime ideal_ of $Lambda$ is a proper two-sided ideal $frak(P)$ in $Lambda$,
such that $K dot frak(P) = A$, and such that for every pair of two-sided ideals
$S, T$ in $Lambda$, #idx("prime ideal")#idx("ideal", "prime")
$
  S dot T subset frak(P) ==> S subset frak(P) quad "or" quad T subset frak(P).
$ <eq:prime-ideal-condition>
There is no loss of generality in imposing this condition only for the special
case where both $S$ and $T$ contain $frak(P)$; for if @eq:prime-ideal-condition
holds in this special case, then in the general case we have
$
  S dot T subset frak(P) & ==> (S + frak(P))(T + frak(P)) subset frak(P)
  ==> S + frak(P) subset frak(P) quad "or" quad T + frak(P) subset frak(P) \
  & ==> S subset frak(P) quad "or" quad T subset frak(P).
$
Hence @eq:prime-ideal-condition is equivalent to the following condition: for
each pair of two-sided ideals $J, J'$ in $Lambda slash frak(P)$,
$
  J dot J' = 0 ==> J = 0 quad "or" quad J' = 0.
$ <eq:prime-ideal-quotient-condition>

#theorem[
  The prime ideals of $Lambda$ coincide with the maximal two-sided ideals of
  $Lambda$. If $frak(P)$ is a prime ideal of $Lambda$, then
  $P = frak(P) inter R$ is a (nonzero) prime ideal #source(200)of $R$, and
  $overline(Lambda) = Lambda slash frak(P)$ is a finite dimensional simple
  algebra over the field $R slash P$.
] <th:prime-ideals-maximal>

#proof[
  Let $frak(P)$ be a prime ideal of $Lambda$, and set $P = frak(P) inter R$,
  $overline(Lambda) = Lambda slash frak(P)$. Since $frak(P)$ is a full
  $R$-lattice in $A$, we have $P != 0$. On the other hand, $P < R$ since
  $1 in.not frak(P)$. If $alpha, beta in R$, then
  $
    alpha beta in P & ==> alpha Lambda dot beta Lambda subset frak(P)
    ==> alpha Lambda subset frak(P) quad "or" quad beta Lambda subset frak(P) \
    & ==> alpha in P quad "or" quad beta in P.
  $
  Thus $P$ is a prime ideal of $R$, and $overline(Lambda)$ is a finite
  dimensional algebra over the field $R slash P$.

  Next we observe that $rad overline(Lambda)$ is nilpotent, since
  $overline(Lambda)$ is artinian. Thus $rad overline(Lambda) = 0$ by
  @eq:prime-ideal-quotient-condition, and so $overline(Lambda)$ is semisimple.
  However, the simple components of $overline(Lambda)$ are two-sided ideals of
  $overline(Lambda)$ which annihilate one another. Hence by
  @eq:prime-ideal-quotient-condition there is only one simple component, that
  is, $overline(Lambda)$ is a simple algebra. Therefore $overline(Lambda)$ has
  no nontrivial two-sided ideals, whence $frak(P)$ is a maximal two-sided ideal
  of $Lambda$.

  Conversely, let $frak(P)$ be any maximal two-sided ideal of $Lambda$. Then
  @eq:prime-ideal-condition automatically holds true when $S$ and $T$ contain
  $frak(P)$, since the only possibilities for $S$ and $T$ are $frak(P)$ and
  $Lambda$. This shows that $frak(P)$ is a prime ideal, and establishes the
  theorem.
]

Keeping the above notation, we prove.

#theorem[
  Let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$. There
  is a one-to-one correspondence $frak(P) <-> P$ between the set of prime ideals
  $frak(P)$ of $Lambda$, and the set of prime ideals $P$ of $R$, given by
  $
    P = R inter frak(P), quad frak(P) = Lambda inter rad Lambda_P.
  $
  Further, $frak(P) dot Lambda_P = rad Lambda_P$, the unique prime ideal of
  $Lambda_P$. For each prime ideal $Q$ of $R$ different from $P$, we have
  $frak(P)_Q = Lambda_Q$.
] <th:prime-ideals-of-maximal-order>

#proof[
  Let $frak(P)$ be a prime ideal of $Lambda$, and set
  $overline(Lambda) = Lambda slash frak(P)$, $P = R inter frak(P)$. Then
  $ann_R overline(Lambda) = P$, so by @th:invertible-action-iso it follows that
  $
    overline(Lambda) tilde.equiv R_P times.o_R overline(Lambda) tilde.equiv
    Lambda_P slash frak(P) dot Lambda_P.
  $
  But $overline(Lambda)$ is a simple ring, and hence $frak(P) dot Lambda_P$ is a
  maximal two-sided ideal of $Lambda_P$. By @th:local-maximal-two-sided-ideals,
  all two-sided ideals of $Lambda_P$ are powers of $rad Lambda_P$. Therefore
  $
    frak(P)_P = frak(P) dot Lambda_P = rad Lambda_P,
  $
  as claimed. Furthermore, $Lambda slash frak(P)$ is torsionfree relative to the
  multiplicative set $R - P$, so by @th:saturated-correspondence we obtain
  $
    frak(P) = Lambda inter frak(P)_P = Lambda inter rad Lambda_P.
  $
  #source(201)Finally, for $Q != P$ we have
  $R_Q times.o_R (Lambda slash frak(P)) = 0$, and thus $frak(P)_Q = Lambda_Q$.

  Conversely, given a prime ideal $P$ of $R$, we may form the two-sided ideal
  $P Lambda$ of $Lambda$. Then $P Lambda != Lambda$, since $Lambda$ is an
  $R$-lattice, and so there exists a maximal two-sided ideal $frak(P)$ of
  $Lambda$ with $P Lambda subset frak(P)$. Clearly $P = R inter frak(P)$, since
  the intersection is a prime ideal of $R$ containing $P$. The preceding
  discussion shows that $frak(P) = Lambda inter rad Lambda_P$, so $P$ uniquely
  determines $frak(P)$. This completes the proof of the theorem.
]

Now let $L$ be any full $R$-lattice in the separable $K$-algebra $A$, and define
$
  L^(-1) = {x in A : L dot x dot L subset L}.
$ <eq:inverse-lattice>
Clearly
$
  L^(-1) = {x in A : L dot x subset O_l (L)}
  = {x in A : x dot L subset O_r (L)}.
$ <eq:inverse-lattice-one-sided>
If $Lambda = O_l (L)$, then $alpha Lambda subset L subset beta Lambda$ for some
nonzero $alpha, beta in R$. Therefore
$alpha^(-1) Lambda supset L^(-1) supset beta^(-1) Lambda$, since
$
  alpha^(-1) Lambda = {x in A : alpha Lambda dot x subset Lambda}
  supset {x in A : L dot x subset Lambda} = L^(-1),
$
and likewise for the other inclusion. Thus $L^(-1)$ is also a full $R$-lattice
in $A$. We shall call $L$ a _full_ left $Lambda$-lattice in $A$, #idx(
  "full lattice",
)to indicate that $L$ is a left $Lambda$-module which is a full $R$-lattice in
$A$. Then $L^(-1)$ is a full right $Lambda$-lattice in $A$.

We may identify $L^(-1)$ with $Hom_Lambda (L, Lambda)$, where $L, Lambda$ are
viewed as left $Lambda$-modules. For each prime ideal $P$ of $R$, $L_P$ is a
full left $Lambda_P$-lattice in $A$. By @th:localization-hom we have
$
  (L^(-1))_P = R_P times.o_R Hom_Lambda (L, Lambda) tilde.equiv
  Hom_(Lambda_P) (L_P, Lambda_P) = (L_P)^(-1).
$
Hereafter, we shall identify $(L^(-1))_P$ with $(L_P)^(-1)$. Likewise, we
identify
$
  hat(R)_P times.o_R L^(-1) quad "and" quad (hat(L)_P)^(-1),
$
where $hat(R)_P$, $hat(L)_P$ are $P$-adic completions of $R$, $L$, respectively.

#theorem[
  Let $L$ be a full left $Lambda$-lattice in $A$, where $Lambda$ is a maximal
  $R$-order in a separable $K$-algebra $A$. Then
  $
    L dot L^(-1) = Lambda, quad L^(-1) dot L = O_r (L), quad
    (L^(-1))^(-1) = L.
  $
] <th:lattice-inverse>

#proof[
  In order to prove that $L dot L^(-1) = Lambda$, it suffices by
  Exercise~@exc:submodules-equal-locally to prove that
  $
    L_P dot (L_P)^(-1) = Lambda_P
  $
  for each $P$. By @th:separable-maximal-principal we may write
  $L_P = Lambda_P y$ for some $y in A$. Then $A = A y$, which implies by
  @th:surjective-endomorphism-noetherian that $y in u(A)$. Therefore
  $
    (L_P)^(-1) = {x in A : Lambda_P y dot x subset Lambda_P} = y^(-1) Lambda_P.
  $
  #source(202)This gives
  $L_P dot L_P^(-1) = Lambda_P y dot y^(-1) Lambda_P = Lambda_P$, as desired,
  and shows that $L dot L^(-1) = Lambda$. The argument also yields the formula
  $
    (L_P)^(-1) dot L_P = y^(-1) Lambda_P y = O_r (L_P)
  $
  for each $P$, whence $L^(-1) dot L = O_r (L)$. Likewise $(L^(-1))^(-1) = L$,
  since this holds locally at each $P$, and the theorem is established.
]

#corollary[
  Keeping the above notation, we have
  $
    O_l (L^(-1)) = O_r (L), quad O_r (L^(-1)) = O_l (L).
  $
] <cor:inverse-lattice-orders>

#proof[
  The first equality holds locally:
  $
    O_l (L_P^(-1)) = O_l (y^(-1) Lambda_P) = y^(-1) Lambda_P y = O_r (L_P).
  $
  Thus the first assertion is correct, and the second follows in the same way.
]

We now repeat several definitions, which were first given in the local case in
§~@sec:ideals-local. All ideals considered below are full $R$-lattices in $A$.
Call a full $R$-lattice $M$ a _normal ideal_ #idx("normal ideal")#idx(
  "ideal",
  "normal",
)if both $O_l (M)$ and $O_r (M)$ are maximal orders. An _integral ideal_ #idx(
  "integral ideal",
)#idx("ideal", "integral")of $A$ is a normal ideal $M$ such that
$M subset O_l (M)$.

#theorem[
  If $M$ is a normal ideal such that $M subset O_l (M)$, then also
  $M subset O_r (M)$, and conversely.
] <th:global-integral-ideal-both-sides>

#proof[
  It suffices to establish the result after localizing at an arbitrary prime
  ideal $P$ of $R$. But the local result has already been proved in
  @th:integral-ideal-both-sides. (See also Exercise~@exc:integral-ideal-direct.)
]

If $M$ is a normal ideal with $O_l (M) = O_r (M) = Lambda$, we shall also refer
to $M$ as a _two-sided $Lambda$-ideal_ in $A$.

#theorem(major: true)[
  Let $Lambda$ be a maximal $R$-order in the central simple $K$-algebra $A$.
  Then the set of two-sided $Lambda$-ideals in $A$ is the free abelian group
  generated by the prime ideals of $Lambda$. The group operation is the usual
  multiplication of lattices, the identity element is $Lambda$, and inverses are
  given by @eq:inverse-lattice.
] <th:two-sided-ideals-free-group>

#proof[
  Let $frak(P)_1, frak(P)_2$ be distinct prime ideals of $Lambda$, and let
  $P_i = frak(P)_i inter R$, so $P_1 != P_2$. For $Q$ any prime ideal of $R$, we
  have
  $
    (frak(P)_i)_Q = cases(
      Lambda_Q"," & Q != P_i",",
      (frak(P)_i)_Q"," & Q = P_i.
    )
  $ <eq:prime-localizations>
  But then $frak(P)_1 dot frak(P)_2 = frak(P)_2 dot frak(P)_1$, since this is
  true locally at _every_ $Q$.

  Now let $M$ be a two-sided $Lambda$-ideal in $A$. Then for each $Q$, $M_Q$ is
  a two-sided #source(203)$Lambda_Q$-ideal in $A$, and so by
  @th:two-sided-ideals-cyclic we have
  $
    M_Q = frak(Q)_Q^(m_Q) quad "for some" quad m_Q in bold(Z),
  $
  where $frak(Q)$ is the prime ideal of $Lambda$ corresponding to $Q$. It should
  be pointed out that the definition of $frak(Q)_Q^(-1)$ given in
  @th:two-sided-ideals-cyclic agrees with the definition of inverse given in
  @eq:inverse-lattice-one-sided. Furthermore, $m_Q = 0$ a.e., since
  $M_Q = Lambda_Q$ a.e. It follows at once that
  $
    M = product_Q frak(Q)^(m_Q),
  $
  since this result holds everywhere locally. Indeed, for any $P$ we have
  $
    M_P = frak(P)_P^(m_P) = product_Q frak(Q)_P^(m_Q),
  $
  by @eq:prime-localizations. Finally, the ideal group is free abelian on the
  generators ${frak(P)}$, since the ideal $M$ uniquely determines the exponents
  in the factorization of $M$. This completes the proof.
]

#corollary[
  The preceding theorem is valid for the more general case where $Lambda$ is a
  maximal $R$-order in a separable $K$-algebra $A$.
] <cor:two-sided-ideals-free-group-separable>

#proof[
  Let $A$ and $Lambda$ be decomposed into components as in
  @th:maximal-orders-components. Then every two-sided $Lambda$-ideal $M$ in $A$
  decomposes into a direct sum $dsum M_i$, where $M_i$ is a two-sided
  $Lambda_i$-ideal in the central simple $K_i$-algebra $A_i$. In particular,
  each maximal two-sided ideal of $Lambda$ is of the form
  $
    Lambda_1 plus.o dots.c plus.o Lambda_(j-1) plus.o frak(P)_j plus.o
    Lambda_(j+1) plus.o dots.c plus.o Lambda_t
  $ <eq:prime-ideal-components>
  for some $j$, $1 <= j <= t$, and some prime ideal $frak(P)_j$ in $Lambda_j$.
  Conversely, each such expression is a prime ideal of $Lambda$. It follows at
  once that if we express $M_j$ as a power product of prime ideals of
  $Lambda_j$, then #display-variant(
    [@eq:prime-ideal-components],
    suffix: "a",
    $
      Lambda_1 plus.o dots.c plus.o Lambda_(j-1) plus.o M_j plus.o
      Lambda_(j+1) plus.o dots.c plus.o Lambda_t
    $,
  ) <eq:ideal-components>
  is a power product of the corresponding prime ideals of $Lambda$ of the form
  @eq:prime-ideal-components. Since $M$ is the product (for $1 <= j <= t$) of
  the expressions in @eq:ideal-components, it is clear that $M$ is a power
  product of prime ideals of $Lambda$. It is then also obvious that the prime
  ideals of $Lambda$ generate a free abelian group, and so the result is proved.
]

We have at our disposal all of the information necessary to describe how a prime
ideal $P$ of $R$ behaves in a maximal $R$-order in a simple $K$-algebra:

#theorem[
  Let $A$ be a central simple $L$-algebra, and let $L$ be a finite separable
  extension of $K$. Let $S$ denote the integral closure of $R$ in $L$, and let
  $Lambda$ be a maximal $R$-order in $A$. Given a prime ideal $P$ of $R$, let
  $P_1, dots, P_d$ be the distinct primes of $S$ dividing $P$, and set #source(
    204,
  )$e_i = e(P_i, L slash K)$. Each $P_i$ determines a prime ideal $frak(P)_i$ of
  $Lambda$ by @th:prime-ideals-of-maximal-order, and we may write
  $
    P_i Lambda = frak(P)_i^(m_i), quad 1 <= i <= d,
  $
  for some positive integers ${m_i}$.
  + The factorization of $P Lambda$ into prime ideals of $Lambda$ is given by
    $
      P Lambda = product_(i=1)^d frak(P)_i^(e_i m_i).
    $
  + For each $i$, $m_i$ is the ramification index of the skewfield part of the
    central simple $hat(L)$-algebra $hat(A)$, where ˆ denotes $P_i$-adic
    completion.
  + If the residue class field $R slash P$ is finite, then for each $i$, $m_i$
    is the index of the skewfield part of $hat(A)$.
] <th:prime-factorization-maximal-order>

#proof[
  From @eq:prime-decomposition we have $P S = product P_i^(e_i)$, whence
  $
    P Lambda = product (P_i Lambda)^(e_i) = product frak(P)_i^(e_i m_i)
  $
  as claimed. Now keep $i$ fixed, and let $hat(L)$, $hat(Lambda)$, $hat(A)$
  denote $P_i$-adic completions. Since $hat(Lambda)$ is a maximal $hat(S)$-order
  in $hat(A)$, by @th:complete-local-maximal-orders we may write
  $
    hat(A) = M_r (D), quad hat(Lambda) = M_r (Delta),
  $
  where $D$ is a skewfield with center $hat(L)$, and $Delta$ is the maximal
  $hat(S)$-order in $D$. If $m$ denotes the ramification index of $D$ over
  $hat(L)$, then by §~@sec:ramification-index-inertial-degree we have
  $
    hat(P)_i Delta = (pi_D Delta)^m,
  $
  where $pi_D$ is a prime element of $Delta$. Therefore
  $
    hat(P)_i hat(Lambda) = M_r (hat(P)_i Delta) = pi_D^m hat(Lambda)
    = (rad hat(Lambda))^m.
  $
  On the other hand, $rad hat(Lambda)$ is the $P_i$-adic completion of
  $frak(P)_i$ by @th:local-maximal-two-sided-ideals. Therefore when we take
  completions on both sides of the equation $P_i Lambda = frak(P)_i^(m_i)$ we
  obtain $hat(P)_i hat(Lambda) = (rad hat(Lambda))^(m_i)$. This shows that
  $m_i = m$, and establishes (ii). Assertion (iii) follows from (ii), by virtue
  of @th:local-skewfield-e-f.
]

Let us turn next to the theory of one-sided ideals in a separable $K$-algebra
$A$. A normal ideal $M$ is called a _maximal integral ideal_ #idx(
  "maximal integral ideal",
)#idx("ideal", "maximal integral")in $A$ if $M$ is a maximal left ideal in its
left order $O_l (M)$.

#theorem[
  For each maximal left ideal $M$ of a maximal $R$-order $Lambda$ in a separable
  $K$-algebra $A$, there is a unique prime ideal $frak(P)$ of $Lambda$ such that
  $
    frak(P) subset M subset Lambda, quad
    frak(P) = ann_Lambda Lambda slash M = {x in Lambda : x Lambda subset M}.
  $ <eq:belongs-to-prime>
  We say that $M$ _belongs_ to $frak(P)$. Then $Lambda slash M$ is a simple left
  module over the simple ring $Lambda slash frak(P)$. Conversely, each $frak(P)$
  determines a maximal left ideal $M$ of $Lambda$ which belongs to $frak(P)$.
] <th:maximal-left-ideal-prime>

#proof[
  #source(205)Given a maximal left ideal $M$ of $Lambda$, we can decompose $M$
  and $Lambda$ according to the decomposition of $A$ into simple components. It
  is then sufficient to prove the result when $A$ is a central simple
  $K$-algebra. Now let $frak(P) = ann_Lambda Lambda slash M$, a two-sided ideal
  of $Lambda$. Choose a nonzero $alpha in R$ such that $alpha Lambda subset M$;
  then $alpha in frak(P)$, so $alpha Lambda subset frak(P)$, and thus
  $Lambda slash frak(P)$ is an artinian ring. But $Lambda slash M$ is a faithful
  left $(Lambda slash frak(P))$-module, and is a simple module. Therefore the
  ring $Lambda slash frak(P)$ is a simple artinian ring, and so $frak(P)$ is a
  prime ideal of $Lambda$, as claimed. Clearly
  $frak(P) = frak(P) Lambda subset M$. Furthermore, if $frak(Q)$ is any
  two-sided ideal of $Lambda$ contained in $M$, then
  $frak(Q) subset ann_Lambda Lambda slash M = frak(P)$. Thus there is a unique
  prime ideal of $Lambda$ contained in $M$.

  Conversely, given a prime ideal $frak(P)$ of $Lambda$, by Zorn's Lemma there
  exists a maximal left ideal $M$ of $Lambda$ such that
  $frak(P) subset M subset Lambda$. Then
  $frak(P) subset ann_Lambda Lambda slash M$, so equality must hold, and thus
  $M$ belongs to $frak(P)$. This completes the proof.
]

#theorem[
  Let $M$ be a normal ideal in the separable $K$-algebra $A$. If $M$ is a
  maximal left ideal of $O_l (M)$, then $M$ is a maximal right ideal of
  $O_r (M)$, and conversely.
] <th:global-maximal-integral-both-sides>

#proof[
  As remarked above, it suffices to prove the result for the special case where
  $A$ is a central simple $K$-algebra. Let $Lambda = O_l (M)$, and let $frak(P)$
  be the prime ideal of $Lambda$ to which $M$ belongs. Setting
  $P = R inter frak(P)$, it is clear that $ann_R Lambda slash M = P$, whence by
  @th:invertible-action-iso we have
  $Lambda_P slash M_P tilde.equiv Lambda slash M$. Thus $M_P$ is a maximal left
  ideal of $Lambda_P$. If we set $Lambda' = O_r (M)$, it then follows from
  @th:maximal-integral-both-sides that $M_P$ is a maximal right ideal of
  $Lambda'_P$.

  On the other hand, let $Q$ be any prime ideal of $R$ different from $P$. Then
  $frak(P)_Q = M_Q = Lambda_Q$, and so
  $
    Lambda'_Q = O_r (M_Q) = Lambda_Q = M_Q.
  $
  Now let $M subset N subset Lambda'$, where $N$ is any right ideal of
  $Lambda'$. Then $M_Q = N_Q$ for $Q != P$, whereas $N_P$ is either $M_P$ or
  $Lambda'_P$. In the former case we see that $N = M$, while in the latter case
  $N = Lambda'$. Thus $M$ is a maximal right ideal of $Lambda'$, and the theorem
  is proved.
]

Let $M, N$ be any pair of full $R$-lattices in the separable $K$-algebra $A$.
Their product $M dot N$ is _proper_ if $O_r (M) = O_l (N)$. Likewise, a product
$M_1 M_2 dots.c M_k$ is called _proper_ if #idx("proper product")
$
  O_r (M_i) = O_l (M_(i+1)), quad 1 <= i <= k - 1.
$
Generalizing @th:proper-product-factorization, we prove

#theorem(major: true)[
  Let $M$ be a full left ideal of the maximal $R$-order $Lambda$ in the
  separable $K$-algebra $A$, and suppose that the $Lambda$-module
  $Lambda slash M$ has composition length $k$. Then $M$ is expressible as a
  proper product of $k$ maximal integral ideals $M_1 dots.c M_k$, such that
  $
    O_l (M) = O_l (M_1), quad O_r (M) = O_r (M_k).
  $
] <th:global-proper-product-factorization>

#proof[
  #source(206)Use induction on $k$, the result being trivial when $k = 1$.
  Assume that $k > 1$, and that the theorem is known for the case $k - 1$. We
  can choose a maximal left ideal $N$ of $Lambda$ such that
  $M subset N subset Lambda$, and then $N slash M$ has composition length
  $k - 1$ as left $Lambda$-module. Both $M$ and $N$ are normal ideals, with left
  order $Lambda$. By @th:lattice-inverse we have
  $
    N dot N^(-1) = Lambda, quad N^(-1) dot N = O_r (N) = Lambda' "(say)".
  $

  Now there is a bijection $W -> N^(-1) W$ between the set of left
  $Lambda$-submodules $W$ of $N$, and the set of left $Lambda'$-submodules
  $N^(-1) W$ of $Lambda'$, with the inverse mapping given by
  $N^(-1) W -> N (N^(-1) W)$. Therefore $N^(-1) M$ is a left ideal of $Lambda'$,
  and the quotient $Lambda' slash N^(-1) M$ has composition length $k - 1$ as
  left $Lambda'$-module. It follows from the induction hypothesis that we may
  write
  $
    N^(-1) M = M_2 dots.c M_k,
  $
  a proper product of $k - 1$ maximal integral ideals, with
  $
    O_l (M_2) = O_l (N^(-1) M) = Lambda', quad
    O_r (M_k) = O_r (N^(-1) M) = O_r (M).
  $
  But then $M = N M_2 dots.c M_k$ is the desired proper product of $k$ maximal
  integral ideals, and the theorem is proved.
]

We shall next prove the non-commutative analogue of the algebraic number theory
dictum "To contain is to divide" (see H.~Cohn [@bib:Cohn1962]). In the proof, it
will be convenient to use the notation $N = N_(i j)$ to indicate that the normal
ideal $N$ has left order $Lambda_i$ and right order $Lambda_j$. Thus a proper
product might be written as $N_12 N_23$, where $Lambda_1, Lambda_2$ and
$Lambda_3$ need not be distinct. From @cor:inverse-lattice-orders we obtain
$
  (N_(i j))^(-1) = (N^(-1))_(j i), quad N dot N^(-1) = Lambda_i, quad
  N^(-1) dot N = Lambda_j.
$

#theorem[
  + A proper product of integral ideals is integral.
  + Let $M_12, N_14$ be normal ideals with the same left order $Lambda_1$. Then
    $M subset N$ if and only if $M_12 = N_14 dot C_42$ for some integral ideal
    $C$.
  + Let $M_12, N_34$ be normal ideals. Then $M subset N$ if and only if $M$ is a
    proper product
    $
      M_12 = B_13 N_34 C_42
    $ <eq:contain-is-to-divide>
    for some integral ideals $B, C$.
] <th:to-contain-is-to-divide>

#proof[
  To prove (i), we show by induction on $k$ that
  $
    M_12 M_23 dots.c M_(k,k+1) subset Lambda_(k+1),
  $
  if the $M$'s are integral ideals. The result is clear for $k = 1$, so let
  $k > 1$, and assume the result for $k - 1$ factors. Then
  #source(207)
  $
    M_12 dots.c M_(k-1,k) M_(k,k+1) subset Lambda_k M_(k,k+1) = M_(k,k+1)
    subset Lambda_(k+1),
  $
  as desired.

  We next prove (iii), since (ii) will then follow as a special case. If
  @eq:contain-is-to-divide holds with $B, C$ integral, then
  $
    M_12 subset Lambda_3 N_34 Lambda_4 = N_34,
  $
  as claimed. Conversely, let $M_12 subset N_34$, and set
  $
    B_13 = M_12 (Lambda_3 M_12)^(-1), quad C_42 = (N_34)^(-1) M_12.
  $
  It is easily verified that $B, C$ are normal ideals with the indicated orders.
  Next, the normal ideals $M$ and $Lambda_3 M$ have the same right order, and
  $M subset Lambda_3 M$, so by @eq:inverse-lattice-one-sided we obtain
  $M^(-1) supset (Lambda_3 M)^(-1)$. Therefore
  $B subset M dot M^(-1) = Lambda_1$, and hence $B$ is integral. Further,
  $C = N^(-1) M subset N^(-1) N = Lambda_4$, so $C$ is also integral. Finally,
  $
    B_13 N_34 C_42 & = M (Lambda_3 M)^(-1) dot N dot N^(-1) M
                     = M (Lambda_3 M)^(-1) dot Lambda_3 M \
                   & = M dot Lambda_2 = M,
  $
  which completes the proof of (iii). To prove (ii), note that when
  $Lambda_1 = Lambda_3$, we obtain $B = M (Lambda_1 M)^(-1) = Lambda_1$ in the
  above. This establishes the theorem. Of course, the analogue of (ii) holds for
  a pair of normal ideals with the same right order.
]

Let us now investigate the uniqueness properties of the factorization of an
integral ideal into a proper product of maximal integral ideals. As we have
already seen in Exercises~@exc:maximal-integral-noncommuting and
@exc:non-unique-factorization, the factors need not commute, and there may be
more than one possible factorization. To some extent, the difficulty arises from
the fact that we must consider not just one maximal order, but the sequence of
maximal orders associated with the successive factors. Let us prove some results
on change of orders.

#theorem[
  Let $Lambda_1, Lambda_2$ be a pair of maximal $R$-orders in the separable
  $K$-algebra $A$. Then there exists a normal ideal $M = M_12$. If $I(Lambda_j)$
  denotes the group of two-sided $Lambda_j$-ideals in $A$ ($j = 1, 2$), there is
  an isomorphism
  $
    phi_12 : I(Lambda_1) tilde.equiv I(Lambda_2), quad "where" quad
    phi_12 (X) = M^(-1) X M, quad X in I(Lambda_1).
  $
  The map $phi_12$ is independent of the choice of $M_12$.
] <th:two-sided-ideal-groups-isomorphic>

#proof[
  The product $M = Lambda_1 dot Lambda_2$ is a normal ideal with left order
  $Lambda_1$ and right order $Lambda_2$. It is clear that $phi_12$ carries
  $I(Lambda_1)$ into $I(Lambda_2)$, taking $Lambda_1$ onto $Lambda_2$. If $N_12$
  is another normal ideal, then $M N^(-1) in I(Lambda_1)$. Since $I(Lambda_1)$
  is abelian, it follows that $M N^(-1)$ commutes with each $X in I(Lambda_1)$,
  and hence $M^(-1) X M = N^(-1) X N$. Therefore $phi_12$ does not depend on the
  choice of the normal ideal #source(208)$M_12$ used to define $phi_12$.
  Finally, $phi_12$ is an isomorphism since it has an inverse $phi_21$, given by
  $phi_21 (Y) = M Y M^(-1)$, $Y in I(Lambda_2)$. This completes the proof.
]

#corollary[
  Let $M_12$ be a maximal integral ideal which belongs to the prime ideal
  $frak(P)_1$ of $Lambda_1$, and to the prime ideal $frak(P)_2$ of $Lambda_2$.
  Then $frak(P)_2 = phi_12 (frak(P)_1)$.
] <cor:maximal-integral-ideal-similar-primes>

#proof[
  It is clear from @th:two-sided-ideal-groups-isomorphic that
  $phi_12 (frak(P)_1)$ is a prime ideal of $Lambda_2$, and that
  $phi_12 (frak(P)_1) = M^(-1) frak(P)_1 M$. We have
  $
    frak(P)_1 subset M => M^(-1) subset frak(P)_1^(-1)
    => M^(-1) frak(P)_1 M subset frak(P)_1^(-1) frak(P)_1 M = M.
  $
  Thus $phi_12 (frak(P)_1)$ is a prime ideal of $Lambda_2$ contained in $M$,
  whence $M$ belongs to $phi_12 (frak(P)_1)$. This completes the proof.
]

#corollary[
  Let $M_23$ be a maximal integral ideal belonging to the prime ideal
  $frak(P)_2$ of $Lambda_2$. Then for each normal ideal $B = B_12$, the quotient
  $B_12 slash B_12 M_23$ is a simple left $Lambda_1$-module, and
  $
    ann_(Lambda_1) B slash B M = {x in Lambda_1 : x B subset B M}
    = phi_21 (frak(P)_2).
  $
] <cor:simple-quotient-annihilator>

#proof[
  If $B M subset X subset B$ is a chain of left $Lambda_1$-modules, then
  $M subset B^(-1) X subset Lambda_2$ is a chain of left $Lambda_2$-modules.
  Thus $B^(-1) X$ is either $M$ or $Lambda_2$, whence $X$ is either $B M$ or
  $B$. This shows that $B slash B M$ is a simple left $Lambda_1$-module. As in
  the proof of @th:maximal-left-ideal-prime, $ann_(Lambda_1) B slash B M$ is a
  prime ideal of $Lambda_1$. But $phi_21 (frak(P)_2) = B frak(P)_2 B^(-1)$ is a
  prime ideal of $Lambda_1$ which annihilates $B slash B M$. Therefore
  $ann_(Lambda_1) B slash B M = phi_21 (frak(P)_2)$, and the corollary is
  established.
]

Let $phi_12 : I(Lambda_1) tilde.equiv I(Lambda_2)$ be the isomorphism described
in @th:two-sided-ideal-groups-isomorphic. For $X in I(Lambda_1)$, we call the
ideals $X$ and $phi_12 (X)$ _similar_.#idx("similar ideals") Thus, by
@cor:maximal-integral-ideal-similar-primes, each maximal integral ideal
determines a pair of similar prime ideals. We may caution that the converse need
not hold, that is, given a pair of similar prime ideals $frak(P)_1$ and
$frak(P)_2$, it is not necessarily true (even in the complete local case) that
there exists a maximal integral ideal $M_12$ belonging to both $frak(P)_1$ and
$frak(P)_2$ (see Exercise~@exc:similar-primes-no-common-ideal).

We are now ready to deal with the uniqueness properties of factorizations into
proper products of maximal integral ideals, still assuming that $A$ is any
separable $K$-algebra.

#theorem[
  In any factorization of an integral ideal $L$ into a proper product of maximal
  integral ideals, the number of factors is uniquely determined by $L$, and the
  prime ideals to which these factors belong are uniquely determined up to
  similarity and order of occurrence.
] <th:factorization-uniqueness>

#proof[
  Let $L = L_(1r)$ be an integral ideal, and suppose that
  #source(209)
  $
    L_(1r) = M_12 M_23 dots.c M_(k r),
  $ <eq:maximal-factorization>
  where each $M_(i,i+1)$ is a maximal integral ideal, and $M_(k,k+1)$ is
  interpreted to be $M_(k r)$. By @cor:simple-quotient-annihilator, the chain of
  left $Lambda_1$-modules
  $
    Lambda_1 supset M_12 supset M_12 M_23 supset dots.c supset
    M_12 M_23 dots.c M_(k r) = L_(1r)
  $ <eq:maximal-factorization-chain>
  is strictly decreasing, and is unrefinable. The factor modules
  $
    Lambda_1 slash M_12, M_12 slash M_12 M_23, dots,
  $ <eq:maximal-factorization-quotients>
  are therefore the composition factors of the left $Lambda_1$-module
  $Lambda_1 slash L$. By the Jordan–Hölder Theorem, these composition factors
  are uniquely determined by $L$, up to $Lambda_1$-isomorphism and order of
  occurrence.

  There are $k$ such factor modules, so $L$ determines $k$ uniquely.
  Furthermore, let $frak(P)_i$ denote the prime ideal of $Lambda_i$ to which
  $M_(i,i+1)$ belongs, $1 <= i <= k$. Then by @cor:simple-quotient-annihilator
  we have
  $
    frak(P)_1 = ann_(Lambda_1) Lambda_1 slash M_12, quad
    phi_21 (frak(P)_2) = ann_(Lambda_1) M_12 slash M_12 M_23, dots.
  $
  Thus $L$ uniquely determines the set of prime ideals of $Lambda_1$
  $
    {frak(P)_1, phi_21 (frak(P)_2), dots, phi_(k 1) (frak(P)_k)}.
  $
  This completes the proof of the theorem.
]

As already remarked in Exercises~@exc:maximal-integral-noncommuting and
@exc:non-unique-factorization, the individual factors $M_(i,i+1)$ occurring in
@eq:maximal-factorization are not uniquely determined (except in special cases).
Indeed, even the set of maximal orders ${Lambda_2, dots, Lambda_k}$ is not an
invariant of $L$. We now prove, however, that the order of occurrence of the
composition factors of $Lambda_1 slash L$ in @eq:maximal-factorization-quotients
may be specified in advance.

#theorem[
  Let $L$ be a left ideal of the maximal $R$-order $Lambda$ in a separable
  $K$-algebra $A$, and let ${S_1, dots, S_k}$ be the composition factors of the
  $Lambda$-module $Lambda slash L$, arranged in any preassigned order. Then
  there is a factorization @eq:maximal-factorization of $L$ into a product of
  maximal integral ideals, such that the factor modules in
  @eq:maximal-factorization-quotients are precisely $S_1, dots, S_k$, in that
  order.
] <th:factorization-preassigned-order>

#proof[
  Any composition series for the left $Lambda$-module $Lambda slash L$ lifts to
  an unrefinable chain of left ideals of $Lambda$, and this chain can be
  expressed in the form @eq:maximal-factorization-chain for some choice of $M$'s
  (by @th:to-contain-is-to-divide). Hence it suffices to prove that
  $Lambda slash L$ has a composition series in which the composition factors
  occur in the preassigned order $S_1, dots, S_k$. Furthermore, a decomposition
  of $A$ into simple components yields corresponding decompositions of $Lambda$
  and $L$, and hence of $Lambda slash L$. It is therefore sufficient to deal
  with the case where $A$ is a central simple $K$-algebra.

  Let us set $T = Lambda slash L$, an $R$-torsion finitely generated left
  $Lambda$-module, and let #source(210)$frak(A) = ann_Lambda T$. Then $frak(A)$
  is a two-sided ideal of $Lambda$, and so we may write
  $frak(A) = product_1^n frak(P)_i^(a_i)$, where the ${frak(P)_i}$ are distinct
  prime ideals of $Lambda$. Then $T$ is a left $(Lambda slash frak(A))$-module.
  But
  $
    Lambda slash frak(A) tilde.equiv dsum_1^n Lambda slash frak(P)_i^(a_i),
  $
  whence there is a decomposition $T = dsum_1^n T_i$, with
  $
    T_i = {x in T : frak(P)_i^(a_i) x = 0}
    = {x in T : frak(P)_i^m x = 0 "for some" m}.
  $
  (Call $T_i$ the _$frak(P)_i$-primary component_ of $T$.)
  #idx("primary component")

  It suffices to show that the left $Lambda$-module $T_i$ has a composition
  series in which the factors occur in a preassigned order. Each composition
  factor $X$ of $T_i$ is a simple left $Lambda$-module, hence as in
  @th:maximal-left-ideal-prime, $ann_Lambda X$ is a prime ideal of $Lambda$. But
  then $ann_Lambda X = frak(P)_i$, since we already know that
  $frak(P)_i^(a_i) X = 0$. Hence $X$ is a simple left
  $(Lambda slash frak(P)_i)$-module. Since $Lambda slash frak(P)_i$ is a simple
  artinian ring, there is only one isomorphism class of such modules $X$. Thus
  all of the composition factors of $T_i$ are mutually isomorphic. This proves
  that $T_i$ has a composition series with preassigned order of composition
  factors (indeed, any composition series of $T_i$ will do), and thus the same
  holds true for $Lambda slash L$. The theorem is thus established.
]

To conclude this section, we observe that the collection of normal ideals in a
separable $K$-algebra forms a groupoid, according to the following definition. A
_groupoid_ $G$ is a collection of elements, certain of whose products are
defined and lie in $G$, such that #idx("groupoid")
+ For each $a_(i j) in G$, there exist unique elements $e_i, e_j in G$ such that
  $e_i a_(i j) = a_(i j) = a_(i j) e_j$, where all indicated products are
  defined. Further, $e_i e_i = e_i$, $e_j e_j = e_j$. Call $e_i$ the _left unit_
  of $a_(i j)$, and $e_j$ the _right unit_ of $a_(i j)$.
+ $a_(i j) b_(k l)$ is defined if and only if $j = k$, that is, if and only if
  the right unit of $a_(i j)$ equals the left unit of $b_(k l)$.
+ If $a b$ and $b c$ are defined, so are $(a b) c$ and $a (b c)$, and these are
  equal.
+ For each $a_(i j) in G$, there exists an $a_(i j)^(-1) in G$ with left unit
  $e_j$, right unit $e_i$, such that
  $
    a_(i j) dot a_(i j)^(-1) = e_i, quad a_(i j)^(-1) dot a_(i j) = e_j.
  $
+ Given any pair of units $e, e' in G$, there is an element $a_(i j) in G$ with
  left unit $e$, right unit $e'$.

The collection of all normal ideals in $A$, relative to proper multiplication,
is the _Brandt groupoid_ associated with $A$.#idx("Brandt groupoid") The units
are the maximal orders in $A$; the inverse of a normal ideal $M$ is the normal
ideal $M^(-1)$. If $Lambda$ and $Lambda'$ are maximal orders, the normal ideal
$Lambda dot Lambda'$ has left unit $Lambda$, right unit $Lambda'$.

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#source(211)Unless otherwise stated, $Lambda$ denotes a maximal $R$-order in a
separable $K$-algebra $A$.

#exercise[
  Let $R$ be a complete discrete valuation ring with prime element $pi$, and let
  $
    Lambda_1 = M_3 (R), quad Lambda_2 = y Lambda_1 y^(-1), quad "where" quad
    y = diag(1, 1, pi) in Lambda_1.
  $
  Show that no maximal left ideal of $Lambda_1$ can be a maximal right ideal of
  $Lambda_2$. Deduce from this that the prime ideals $pi Lambda_1$,
  $pi Lambda_2$ are similar, but that there is no maximal integral ideal $M_12$
  which belongs to both $pi Lambda_1$ and $pi Lambda_2$.
  #hint[@exc:similar-primes-no-common-ideal][Let $Lambda_1 x$ be a maximal left
    ideal of $Lambda_1$, and suppose that $O_r (Lambda_1 x) = Lambda_2$. Then
    $Lambda_2 = x^(-1) Lambda_1 x$, so
    $
      (x y) dot Lambda_1 dot (x y)^(-1) = Lambda_1.
    $
    Therefore (see Exercise~@exc:matrix-order-normalizer) $x y = pi^k u$ for
    some $k >= 1$ and some $u in u(Lambda_1)$. But then $x$ has elementary
    divisors ${pi^(k-1), pi^k, pi^k}$, which contradicts
    @th:complete-local-maximal-right-ideals.]
  <hint:similar-primes-no-common-ideal>
] <exc:similar-primes-no-common-ideal>

#exercise[
  Let $M, N$ be normal ideals in $A$. Prove that $M dot N$ is a proper product
  if and only if replacing either factor by a larger $R$-lattice (in $A$)
  increases the product. #hint[@exc:proper-product-criterion][Let $M = M_12$,
    $N = N_34$, in the notation introduced just before
    @th:to-contain-is-to-divide. Suppose that increasing either factor increases
    the product $M N$. Then
    $
      M N = M Lambda_2 dot N = M dot Lambda_2 N ==> N = Lambda_2 N
      ==> Lambda_2 = Lambda_3.
    $
    Conversely, let $Lambda_2 = Lambda_3$ and let $M' N = M N$, where $M'$ is an
    $R$-lattice properly containing $M$. Then
    $
      M' subset M' Lambda_2 = M' dot N N^(-1) = M dot N N^(-1) = M,
    $
    a contradiction.] <hint:proper-product-criterion>
] <exc:proper-product-criterion>

#exercise[
  Let $frak(P)_1, dots, frak(P)_n$ be distinct prime ideals of $Lambda$. Let
  $
    frak(A) = product_1^n frak(P)_i^(a_i), quad
    frak(B) = product_1^n frak(P)_i^(b_i), quad a_i, b_i in bold(Z).
  $
  Prove
  + $frak(A) supset frak(B)$ if and only if $a_i <= b_i$, $1 <= i <= n$.
  + $frak(A) + frak(B) = product_1^n frak(P)_i^(min(a_i, b_i))$.
  + $frak(A) inter frak(B) = product_1^n frak(P)_i^(max(a_i, b_i))$.
  + If each $a_i >= 0$, then there is a ring isomorphism
    $
      Lambda slash frak(A) tilde.equiv
      dsum_(i=1)^n Lambda slash frak(P)_i^(a_i).
    $
] <exc:prime-power-products>

#exercise[
  Show that each finitely generated $R$-torsion left $Lambda$-module $X$ is
  expressible as a finite direct sum $dsum Lambda slash J_i$, where each $J_i$
  is a left ideal of $Lambda$ of the same $R$-rank as $Lambda$.
  #hint[@exc:torsion-modules-cyclic][As in the proof of
    @th:factorization-preassigned-order, the problem reduces to the case where
    $R$ is a complete discrete valuation ring, and where $Lambda = M_k (Delta)$
    for some maximal $R$-order $Delta$ in a skewfield. By means of the Morita
    correspondence, the problem further reduces to that of finding $R$-torsion
    $Delta$-modules. Now use
    @th:skewfield-matrix-diagonalization.] <hint:torsion-modules-cyclic>
] <exc:torsion-modules-cyclic>

#exercise[
  #source(212)Any simple left $Lambda$-module is of the form $Lambda slash M$,
  where $M$ is a maximal left ideal of $Lambda$. Let $P = R inter M$. Show that
  $P$ is a prime ideal of $R$, and that $P = ann_R Lambda slash M$.
  #hint[@exc:simple-module-prime][Use @th:prime-ideals-maximal.]
  <hint:simple-module-prime>
] <exc:simple-module-prime>

#exercise[
  Let $M_23$ be a maximal integral ideal, and $B_12$ any normal ideal. Prove
  that
  $
    ann_R Lambda_2 slash M_23 = ann_R B_12 slash B_12 M_23.
  $
  #hint[@exc:annihilator-similar-quotients][If $P = ann_R Lambda_2 slash M$,
    then $P B^(-1) B = P Lambda_2 subset M_23$, whence $P B subset B M$.]
  <hint:annihilator-similar-quotients>
] <exc:annihilator-similar-quotients>

#exercise[
  Keeping the notation of @th:factorization-preassigned-order, let
  $frak(P)_i = ann_Lambda S_i$, $P_i = frak(P)_i inter R = ann_R S_i$,
  $1 <= i <= k$. Let $P_1, dots, P_n$ be the distinct prime ideals of $R$ among
  ${P_1, dots, P_k}$. Show that we can express $L$ as a proper product
  $
    L = N^((1)) dot N^((2)) dots.c N^((n)),
  $
  where each $N^((i))$ is an integral ideal such that
  $
    (N^((i)))_(P_i) = L_(P_i), quad (N^((i)))_P = "maximal order" quad
    (P != P_i),
  $
  for $1 <= i <= n$.
] <exc:primary-factorization>

#exercise[
  Let $L, M$ be left ideals in $Lambda$ such that
  $
    ann_R Lambda slash L + ann_R Lambda slash M = R.
  $
  Show that there exists a left ideal $N$ such that
  $
    Lambda slash N tilde.equiv Lambda slash L dotplus Lambda slash M.
  $
  #hint[@exc:coprime-quotients-sum][Define a left $Lambda$-homomorphism
    $
      f : Lambda -> Lambda slash L dotplus Lambda slash M
    $
    by $f(lambda) = (lambda + L, lambda + M)$, $lambda in Lambda$. For each
    prime ideal $P$ of $R$, either $(Lambda slash L)_P = 0$ or
    $(Lambda slash M)_P = 0$. Thus $f_P$ is epic for each $P$, whence also $f$
    is epic. Now choose $N = ker f$.] <hint:coprime-quotients-sum>
] <exc:coprime-quotients-sum>

#exercise[
  Prove @th:global-integral-ideal-both-sides directly.
  #hint[@exc:integral-ideal-direct][$M subset O_l (M) => M dot M subset M
    => M subset O_r (M)$.] <hint:integral-ideal-direct>
] <exc:integral-ideal-direct>

#exercise[
  Verify that the definition of inverses in @th:two-sided-ideals-cyclic agrees
  with the definition in @eq:inverse-lattice-one-sided.
] <exc:inverse-definitions-agree>

#exercise[
  Show that any two maximal orders $Lambda_1, Lambda_2$ in $A$ are Morita
  equivalent. #hint[@exc:maximal-orders-morita-equivalent][(1) Reduce to central
    simple case, then use @cor:global-maximal-morita and transitivity of Morita
    equivalence; or (2) Let $M = M_12$ be a normal ideal, and identify
    $Hom_(Lambda_1) (M, Lambda_1)$ with the module of right multiplications by
    elements of $M^(-1)$. The formula $M dot M^(-1) = Lambda_1$ is then
    equivalent to the assertion that
    $
      mu : M times.o_(Lambda_2) Hom_(Lambda_1) (M, Lambda_1) -> Lambda_1
    $
    is an epimorphism. Likewise,
    $
      tau : Hom_(Lambda_1) (M, Lambda_1) times.o_(Lambda_1) M -> Lambda_2
    $
    is epic. Hence $Lambda_1$ and $Lambda_2$ are Morita equivalent by
    §~@sec:morita-correspondence.] <hint:maximal-orders-morita-equivalent>
] <exc:maximal-orders-morita-equivalent>

#exercise[
  Let $Gamma$ be an arbitrary $R$-order in a central simple $K$-algebra $A$.
  Show that $Gamma$ is a maximal order if and only if $Gamma$ is hereditary, and
  for each prime ideal $P$ of $R$ there is a unique prime ideal of $Gamma$
  containing $P$. #hint[@exc:maximal-order-criterion][To prove $Gamma$ maximal,
    it suffices to prove $Gamma_P$ maximal for each $P$. There is a one-to-one
    correspondence between the #source(213)prime ideals of $Gamma$ containing
    $P$, and the prime ideals of $Gamma_P$. Now use
    @th:auslander-goldman-local-criterion.] <hint:maximal-order-criterion>
] <exc:maximal-order-criterion>

#exercise[
  Let $P$ be a prime ideal of $R$, and let $P Lambda = product frak(P)_i^(e_i)$,
  where the $frak(P)_i$ are prime ideals of the maximal order $Lambda$. Let
  $f_i = (Lambda slash frak(P)_i : R slash P)$. Prove that
  $
    sum e_i f_i = (A : K).
  $
  #hint[@exc:sum-ef-maximal-order][Consider the $overline(R)$-algebra
    $Lambda slash P Lambda$, where $overline(R) = R slash P$, and imitate the
    proof of @th:sum-ef.] <hint:sum-ef-maximal-order>
] <exc:sum-ef-maximal-order>
