#import "main-defs.typ": *
#import "statements.typ": *

== Ideal classes; Jordan–Zassenhaus theorem <sec:ideal-classes>

Throughout this section let $R$ denote a Dedekind domain whose quotient field
$K$ is a global field. As shown in the references listed in
§~@sec:dedekind-domains, the ring $R slash R alpha$ is finite for each nonzero
$alpha in R$. Let us set
$
  abs(alpha) = card R slash R alpha, quad alpha != 0; quad abs(0) = 0.
$

Let $Lambda$ be an $R$-order in a $K$-algebra $A$. By a _left $Lambda$-ideal_ in
$A$ we shall mean, as usual, a left $Lambda$-lattice $M$ in $A$ such that
$K M = A$. We may partition the set of left $Lambda$-ideals in $A$ into ideal
classes, by placing two such ideals $M, N$ in the same class if
$M tilde.equiv N$ as left $Lambda$-modules. Each such isomorphism extends to a
left $A$-isomorphism $K M tilde.equiv K N$, hence is given by right
multiplication by some $x in u(A)$. Thus the _ideal class_#idx("ideal", "class")
containing $M$ consists of all ideals ${M x : x in u(A)}$. We shall show that
under suitable hypotheses, the number $h(Lambda)$ of ideal classes of $Lambda$
is finite.#idx("ideal", "class number") This result will be a special case of
the more general Jordan–Zassenhaus Theorem proved below, and will be valid for
all orders, not just for maximal orders. As we shall see, the general case
reduces quickly to the case of ideals. We shall follow the treatment in
Swan–Evans [@bib:Swan1970]; another approach is given in Curtis–Reiner
[@bib:Curtis1962].

Given an $R$-order $Lambda$, we shall say that the _Jordan–Zassenhaus condition_
$J Z(Lambda)$#idx("Jordan–Zassenhaus condition") holds true if for each positive
integer $t$, there are only finitely many $Lambda$-isomorphism classes of left
$Lambda$-lattices of $R$-rank at most $t$. We intend to prove that $J Z$ holds
for _all_ $R$-orders in semisimple $K$-algebras.
Exercise~@exc:jordan-zassenhaus-fails shows that the restriction to semisimple
algebras cannot be omitted.

Our first lemma shows that in order to test whether $J Z(Lambda)$ holds true, it
suffices to test for $J Z(Delta)$, with $Delta$ ranging over orders in
skewfields.

#lemma[
  Let $Lambda$ be an $R$-order in the semisimple $K$-algebra $A$, let $D_i$ be
  the skewfield part of the $i$-th simple component of $A$, and let $Delta_i$ be
  an $R$-order in $D_i$. If $J Z(Delta_i)$ holds for each $i$, then
  $J Z(Lambda)$ also holds true.
] <lem:jordan-zassenhaus-reduction>

#proof[
  To begin with, let $Gamma$ be another $R$-order in $A$ such that
  $Gamma subset Lambda$. Any #source(234)two left $Lambda$-lattices $M, N$ are
  also left $Gamma$-lattices, and
  $
    K times.o_R Hom_Gamma (M, N) tilde.equiv Hom_A (K M, K N)
    tilde.equiv K times.o_R Hom_Lambda (M, N).
  $
  Thus $M tilde.equiv N$ as $Lambda$-lattices if and only if there exists an
  $A$-isomorphism $phi: K M tilde.equiv K N$ such that $phi(M) = N$. Since this
  condition is independent of $Lambda$, it follows that $M$ and $N$ are
  $Lambda$-isomorphic if and only if they are $Gamma$-isomorphic.

  Now let $t$ be any positive integer, and let ${M_i}$ be a collection of left
  $Lambda$-lattices of $R$-rank at most $t$. If $J Z(Gamma)$ holds true, then
  there are only a finite number of $Gamma$-isomorphism classes among the
  ${M_i}$. Hence there are only finitely many $Lambda$-isomorphism classes among
  the ${M_i}$, which shows that $J Z(Lambda)$ is also true.

  We show conversely that if $J Z(Lambda)$ holds, then so does $J Z(Gamma)$.
  Given $t$, let ${L_1, dots, L_f}$ be a full set of representatives of the
  isomorphism classes of left $Lambda$-lattices of $R$-rank at most $t$. For any
  $Gamma$-lattice $M$ of $R$-rank at most $t$, we may view $M$ as embedded in
  $K M$, and then we may form the $Lambda$-lattice $Lambda M$. Since $Lambda M$
  has the same $R$-rank as $M$, it follows that $Lambda M tilde.equiv L_i$ for
  some $i$, $1 <= i <= f$. Replacing $M$ by a $Gamma$-isomorphic copy, we may
  assume that $Lambda M = L_i$. Choose a nonzero $alpha in R$ such that
  $alpha Lambda subset Gamma$; then
  $
    alpha L_i = alpha dot Lambda M subset M subset L_i.
  $
  But $L_i$ is a finitely generated $R$-module, and thus $L_i slash alpha L_i$
  is a finite group, since $R slash alpha R$ is finite for each nonzero
  $alpha in R$. However, $M slash alpha L_i$ is an $R$-submodule of
  $L_i slash alpha L_i$, and thus there are only a finite number of possible
  $M$'s. We have therefore shown that the conditions $J Z(Lambda)$ and
  $J Z(Gamma)$ are equivalent whenever $Gamma subset Lambda$.

  If $Omega$ is any $R$-order in $A$, then $Omega inter Lambda$ is also an
  $R$-order in $A$. Both $J Z(Lambda)$ and $J Z(Omega)$ are equivalent to
  $J Z(Omega inter Lambda)$, and hence are equivalent to each other. This proves
  that if $J Z(Lambda)$ holds for one $R$-order $Lambda$ in $A$, then it holds
  for every $R$-order in $A$.

  Now let $A = dsum M_(n_i) (D_i)$, let $Delta_i$ be an $R$-order in $D_i$, and
  choose $Lambda_i = M_(n_i) (Delta_i)$, $Lambda = dsum Lambda_i$. Each left
  $Lambda$-lattice $M$ decomposes into a direct sum $dsum M_i$, with $M_i$ a
  left $Lambda_i$-lattice. If ${M^((alpha))}$ is some family of left
  $Lambda$-lattices, then for each $alpha$ we may write
  $
    M^((alpha)) = dsum M_i^((alpha)), quad
    M_i^((alpha)) = "left" Lambda_i"-lattice".
  $
  Clearly
  $
    R"-rank" M^((alpha)) = sum_i R"-rank" M_i^((alpha)) quad "for each" alpha.
  $
  Hence the set of positive integers ${R"-rank" M^((alpha))}$ is bounded above
  if and only if for each $i$, the set ${R"-rank" M_i^((alpha))}$ is bounded
  above. We shall usually abbreviate this statement by omitting the superscript
  $alpha$, and shall say "The #source(235)$R$-rank of $M$ is bounded if and only
  if for each $i$, the $R$-rank of $M_i$ is bounded". Thus $J Z(Lambda)$ holds
  true if and only if $J Z(Lambda_i)$ holds for each $i$. By
  §~@sec:morita-correspondence, $Lambda_i$ is Morita equivalent to $Delta_i$,
  and there exists a $(Delta_i, Lambda_i)$-bimodule $L$ such that the
  correspondence $M -> L times.o_(Lambda_i) M$ gives a one-to-one
  isomorphism-preserving correspondence between the set of left
  $Lambda_i$-modules $M$ and the set of left $Delta_i$-modules $L times.o M$.
  This bimodule $L$ is a projective right $Lambda_i$-module, and thus if $M$ is
  an $R$-lattice, so is $L times.o M$. Further, $rank_R M$ is bounded if and
  only if $rank_R L times.o M$ is bounded. It follows at once that
  $J Z(Lambda_i)$ holds true if and only if $J Z(Delta_i)$ holds true. This
  completes the proof of the lemma.
]

#lemma[
  Let $Delta$ be an $R$-order in a skewfield $D$ over $K$. Then $J Z(Delta)$
  holds if and only if the number $h(Delta)$ of ideal classes of $Delta$ is
  finite.#idx("ideal", "class number")
] <lem:jordan-zassenhaus-class-number>

#proof[
  If $J Z(Delta)$ holds, then clearly $h(Delta)$ is finite. Conversely, suppose
  $h(Delta)$ is finite. If $D$ is separable over $K$, then we can show quickly
  that $J Z(Delta)$ holds true. Namely, by the proof of
  @lem:jordan-zassenhaus-reduction, we may assume that $Delta$ is a maximal
  $R$-order in $D$. Then $Delta$ is hereditary, so every left $Delta$-lattice
  $M$ is isomorphic to a direct sum of left ideals of $Delta$. If $rank_R M$ is
  bounded, so is the number of summands. Up to isomorphism, there are only
  $h(Delta)$ possible choices for each summand, whence the number of
  non-isomorphic $M$'s of bounded $R$-rank is finite. Thus $J Z(Delta)$ holds in
  this case.

  Still assuming that $h(Delta)$ is finite, let us drop the assumption that $D$
  is separable over $K$. By @th:lattice-in-free-module, each left
  $Delta$-lattice $M$ may be embedded in a free $Delta$-lattice $Delta^((n))$,
  where $K M = D^((n))$, and then
  $
    rank_R M = (K M : K) = n dot (D : K).
  $
  Let $d = (D : K)$. We show by induction on $t$ that there are only finitely
  many non-isomorphic left $Delta$-lattices of $R$-rank $t d$; this of course
  implies that $J Z(Delta)$ holds true.

  The result is clear for $t = 1$, since we have assumed that $h(Delta)$ is
  finite. Let $t > 1$, and assume the result holds for lattices of $R$-rank
  $(t - 1)d$. If $M$ is any left $Delta$-lattice of $R$-rank $t d$, then by the
  method of proof of @th:hereditary-submodules-of-free, there is a $Delta$-exact
  sequence
  $
    0 -> N -> M -> J -> 0,
  $
  where $J$ is a left ideal of $Delta$, and where $rank_R N = (t - 1)d$. Up to
  isomorphism, there are finitely many choices for $N$ and $J$. Hence (see
  §~@ss:extensions-of-modules) we need only show that for each fixed choice of
  $N$ and $J$, the group $Ext_Delta^1 (J, N)$ is finite. This group is a
  finitely generated $R$-module by @th:finite-generation-hom-ext, so in view of
  our assumptions on $R$, we need only prove that it is an $R$-torsion module,
  that is,
  $
    K times.o_R Ext_Delta^1 (J, N) = 0.
  $
  #source(236)The left-hand expression equals $Ext_D^1 (K J, K N)$ by
  @cor:localization-ext, and hence is zero by @rem:ext-properties[(v)] since
  $K J$ is free as left $D$-module. This completes the proof of the lemma.
]

#lemma[
  Suppose that $R$ is either $bold(Z)$ or a polynomial domain $k[X]$ over a
  finite field $k$. Let $D$ be a skewfield over the quotient field $K$ of $R$.
  Then $J Z(Delta)$ holds true for every $R$-order $Delta$ in $D$.
] <lem:jordan-zassenhaus-pid>

#proof[
  By the preceding lemma, it suffices to prove the finiteness of the number of
  isomorphism classes of left ideals of $Delta$. Since $R$ is a principal ideal
  domain, we may write
  $
    Delta = dsum_(i=1)^n R x_i, quad x_j x_i = sum alpha_(i j l) x_l, quad
    alpha_(i j l) in R.
  $
  Let $x = sum lambda_i x_i in Delta$, $lambda_i in R$. Then
  $
    x_j x = sum_(i, l) lambda_i alpha_(i j l) x_l.
  $
  Hence if $x != 0$, then by Exercise~@exc:index-norm we obtain
  $
    card Delta slash Delta x = abs(N_(D slash K) x)
    = abs(det (sum_i lambda_i alpha_(i j l))_(1 <= j, l <= n)),
  $
  where for nonzero $alpha in R$, $abs(alpha) = card R slash R alpha$. But the
  indicated determinant is a homogeneous polynomial of degree $n$ in the
  $lambda$'s, with coefficients in $R$. It follows from
  Exercise~@exc:absolute-value-properties that there exists a positive constant
  $c$ such that
  $
    abs(lambda_1) <= t, dots, abs(lambda_n) <= t
    => abs(N_(D slash K) (sum lambda_i x_i)) <= c dot t^n.
  $

  Now let $M$ be any proper left ideal of $Delta$. Then $Delta slash M$ is a
  finite group, since it is a finitely generated torsion $R$-module. Let $s$ be
  the greatest integer such that $s^n <= card Delta slash M$, and let
  $lambda_1, dots, lambda_n$ range independently over all elements $lambda in R$
  with $abs(lambda) <= s + 1$. By Exercise~@exc:absolute-value-properties there
  are at least $(s + 1)^n$ such $n$-tuples $(lambda_1, dots, lambda_n)$, and
  thus $sum lambda_i x_i$ ranges over more than $card Delta slash M$ distinct
  elements of $Delta$. Hence two such sums must be congruent mod $M$, and
  therefore $M$ contains a nonzero element
  $
    x = sum_(i=1)^n lambda_i x_i,
  $
  where $lambda_i in R$, and $abs(lambda_i) <= 2(s + 1)$ for each $i$.

  Therefore $Delta x subset M subset Delta$, and
  $
    card Delta slash Delta x = abs(N_(D slash K) (sum lambda_i x_i))
    <= c dot 2^n (s + 1)^n,
  $
  while $card Delta slash M >= s^n$. Hence
  $
    card M slash Delta x & = {card Delta slash Delta x} slash
                           {card Delta slash M} \
                         & <= c dot 2^n (s + 1)^n slash s^n
                           = c dot 2^n (1 + s^(-1))^n <= c dot 4^n.
  $

  #source(237)We have thus shown that every proper left ideal $M$ of $Delta$
  contains a nonzero element $x$ such that $card M slash Delta x <= c dot 4^n$.
  The same holds when $M = Delta$, just choosing $x = 1$. Consider now all
  $R$-modules $T$ having at most $c dot 4^n$ elements. Since $R$ is a principal
  ideal domain, we may express $T$ as a finite direct sum
  $dsum R slash R alpha_i$ where $card R slash R alpha_i <= c dot 4^n$ for each
  $i$. Then each $alpha_i != 0$ since $R$ is infinite, and so
  $abs(alpha_i) <= c dot 4^n$ for each $i$. The number of possible choices for
  the ${alpha_i}$ is therefore finite, by
  Exercise~@exc:absolute-value-properties, and thus there exists a nonzero
  $beta in R$ such that $beta T = 0$ for each $T$. Note that $beta$ does not
  depend on $T$.

  In particular, we have $beta M subset Delta x$ always, and so
  $
    beta dot Delta x subset beta M subset Delta x.
  $
  Therefore
  $
    beta Delta subset M dot beta x^(-1) subset Delta.
  $
  But $beta$ was chosen independently of $M$, and $Delta slash beta Delta$ is
  finite. Hence the number of choices for $M dot beta x^(-1)$ is also finite.
  Since $M tilde.equiv M dot beta x^(-1)$ as left $Delta$-modules, it follows
  that the number of isomorphism classes of left ideals of $Delta$ is finite,
  and the proof is complete.
]

We are now ready to prove the fundamental result

#theorem(major: true, title: [Jordan–Zassenhaus])[
  Let $R$ be any Dedekind domain whose quotient field $K$ is a global field.
  Then for each $R$-order $Lambda$ in a semisimple $K$-algebra $A$, and for each
  positive integer $t$, there are only finitely many isomorphism classes of left
  $Lambda$-lattices of $R$-rank at most $t$.
  #idx("Jordan–Zassenhaus Theorem", target: [@th:jordan-zassenhaus])
] <th:jordan-zassenhaus>

#proof[
  We are trying to prove that $J Z$ holds for $R$-orders in semisimple
  $K$-algebras. We shall first establish the existence of a Dedekind domain
  $R_0$ with quotient field $K$, such that $R_0 subset R$, and such that $J Z$
  holds for $R_0$-orders. When $K$ is an algebraic number field, we choose
  $R_0 = algint {K}$, the integral closure of $bold(Z)$ in $K$. Since
  $bold(Z) subset R$, and $R$ is integrally closed, it follows that
  $R_0 subset R$. By @lem:jordan-zassenhaus-reduction and
  @lem:jordan-zassenhaus-pid, $J Z$ holds for $bold(Z)$-orders. Hence it also
  holds for $R_0$-orders, by Exercise~@exc:jordan-zassenhaus-extension.

  On the other hand, suppose that $K$ is a function field. By definition, we may
  write $K = k(x_1, dots, x_n)$ for some elements $x_1, dots, x_n$, where $k$ is
  a finite field, and where $K$ has transcendence degree 1 over $k$. Each $x_i$
  is expressible as $x_i = y_i slash z_i$ with $y_i, z_i in R$, and therefore
  $K = k(y_1, z_1, dots, y_n, z_n)$. By a theorem of F. K. Schmidt (see
  Zariski–Samuel [@bib:Zariski1958, Th.~31, p.~105]), we may choose one of the
  elements $y_1, z_1, dots, y_n, z_n$ (call the chosen element $X$), such that
  $k(X)$ is purely transcendental over $k$ and $K$ is a finite separable
  extension of $k(X)$. Of course $X in R$, from the manner in which $X$ was
  chosen. Furthermore, the prime field $bold(F)$ of $k$ lies in $R$, and every
  element of $k$ is integral over $bold(F)$. Therefore $R supset k[X]$, and
  hence also $R supset R_0$, where $R_0$ is the integral #source(238)closure of
  $k[X]$ in $K$. By @lem:jordan-zassenhaus-reduction and
  @lem:jordan-zassenhaus-pid, $J Z$ holds for $k[X]$-orders. Hence by
  Exercise~@exc:jordan-zassenhaus-extension, $J Z$ also holds for $R_0$-orders.

  Now let $Lambda$ be any $R$-order in a semisimple $K$-algebra, where $K$ is
  either an algebraic number field or a function field. We have shown above that
  $R$ contains a Dedekind domain $R_0$ with quotient field $K$, such that $J Z$
  holds for $R_0$-orders. By @th:orders-over-larger-ring, there exists an
  $R_0$-order $Lambda_0$ in $A$ such that $Lambda = R Lambda_0$. Further, each
  left $Lambda$-lattice may be expressed as $R M_0$, for some left
  $Lambda_0$-lattice $M_0$. Clearly, the $R$-rank of $R M_0$ equals the
  $R_0$-rank of $M_0$. Since $J Z(Lambda_0)$ holds true, it follows at once that
  $J Z(Lambda)$ is also true. This completes the proof of the theorem.
]

It is worth pointing out another approach to the proof of the Jordan–Zassenhaus
Theorem. Once the theorem is established for $R_0$-orders, it follows for
arbitrary $R$-orders by Exercise~@exc:jordan-zassenhaus-quotients, since it can
be shown (see Swan–Evans [@bib:Swan1970, pp.~226–227]) that $R = S^(-1) R_0$ for
some multiplicative subset $S$ of $R_0$.

Finally, keeping the notation of @th:jordan-zassenhaus, let $L$ be any finite
separable extension of $K$, and let $R'$ be _any_ $R$-order in $L$. Even if $R'$
is not a Dedekind domain, the condition $J Z(Lambda')$ is meaningful for
$R'$-orders $Lambda'$ in semisimple $L$-algebras. The discussion in
Exercise~@exc:jordan-zassenhaus-extension remains valid, and shows that
$J Z(Lambda')$ holds for each such $Lambda'$.

We shall now consider the special case
$
  A = bold(Q) plus.o bold(Q) i plus.o bold(Q) j plus.o bold(Q) k, quad
  Lambda = bold(Z) plus.o bold(Z) i plus.o bold(Z) j plus.o bold(Z) a, & \
                                          a = (1 + i + j + k) slash 2, &
$ <eq:quaternion-maximal-order>
where $Lambda$ is a maximal $bold(Z)$-order in the rational quaternion algebra
$A$. By Exercise~@exc:r-unit-norm, $u(Lambda)$ consists of the 24 elements
$
  plus.minus 1, quad plus.minus i, quad plus.minus j, quad plus.minus k, quad
  (plus.minus 1 plus.minus i plus.minus j plus.minus k) slash 2.
$
It follows readily that for each $x in Lambda$, there exists a unit
$u in u(Lambda)$ such that
$u x in bold(Z) plus.o bold(Z) i plus.o bold(Z) j plus.o bold(Z) k$.

We shall prove that $h(Lambda) = 1$, and indeed that $Lambda$ is a euclidean
domain, though not commutative. Let $x, y in Lambda$, $y != 0$, and write
$
  x y^(-1) = q + r, quad q = alpha_0 + alpha_1 i + alpha_2 j + alpha_3 k, quad
  r = beta_0 + beta_1 i + beta_2 j + beta_3 k,
$
where $alpha_nu in bold(Z)$, $beta_nu in bold(Q)$. We may choose $q$ so that
each $abs(beta_nu) <= 1 slash 2$. Further, if it turns out that each
$abs(beta_nu) = 1 slash 2$, we may change our choice of $q$ and $r$ so that
$q in Lambda$ and $r = 0$. Hence we can always pick $q in Lambda$, $r in A$,
such that
$
  nr r = beta_0^2 + beta_1^2 + beta_2^2 + beta_3^2 < 1.
$
Therefore we may write
$
  x = q y + t, quad "where" quad q, t in Lambda, quad "and" quad
  0 <= nr t < nr y.
$
#source(239)This shows that $Lambda$ has a euclidean algorithm, and consequently
every left ideal in $Lambda$ is principal, and is generated by an element of
smallest reduced norm. Therefore $h(Lambda) = 1$, as claimed.

For orders of class number 1, we can obtain a factorization theory for elements,
rather than for ideals. Let $Lambda$ be any maximal order in a separable
$K$-algebra, with $h(Lambda) = 1$. Let $x in Lambda inter u(A)$; we call $x$
_indecomposable_#idx("indecomposable element") if $x$ is a non-unit of $Lambda$
which cannot be expressed as a product of non-units. We claim that $x$ is
indecomposable if and only if $Lambda x$ is a maximal left ideal of $Lambda$. If
$Lambda x$ is not maximal, then $Lambda x < Lambda m < Lambda$ for some $m$, and
then there is a factorization $x = y m$ into non-units. The procedure can be
reversed, and the claim is established.

Now let $x in Lambda inter u(A)$ be arbitrary, and let
$
  Lambda x = Lambda x_1 < Lambda x_2 < dots.c < Lambda x_n = Lambda
$
be an unrefinable chain of left ideals of $Lambda$, where $x = x_1$ and
$x_n = 1$. Then $x_i = u_i x_(i+1)$ for some $u_i in Lambda$, and
$
  Lambda x_(i+1) slash Lambda x_i tilde.equiv Lambda slash Lambda u_i,
$
so each $u_i$ is indecomposable. The equation
$
  x = u_1 u_2 dots.c u_(n-1)
$
expresses $x$ as a product of $n - 1$ indecomposable elements. The prime ideals
of $Lambda$ associated with these elements are uniquely determined by $x$, up to
similarity and order of occurrence (see @th:factorization-uniqueness).

Returning to the case of quaternions, we use the preceding discussion to prove

#theorem[
  Every positive rational integer is expressible as a sum of four squares.
] <th:four-squares>

#proof[
  Keep the notation of @eq:quaternion-maximal-order, and let $p$ be any rational
  prime. Then there exists a maximal left ideal $M = Lambda m$ such that
  $p Lambda subset M subset Lambda$. Since $A$ is a central simple
  $bold(Q)$-algebra, it follows from @th:reduced-norm-maximal-ideal that
  $
    (nr m) bold(Z) = nr M = p bold(Z).
  $
  Therefore $p = nr m$, since $nr m > 0$.

  Now set $m = alpha_0 + alpha_1 i + alpha_2 j + alpha_3 k$; replacing $m$ by
  $u m$ if need be, where $u in u(Lambda)$, we may assume that each
  $alpha_nu in bold(Z)$. But then
  $
    p = alpha_0^2 + alpha_1^2 + alpha_2^2 + alpha_3^2,
  $
  a sum of four squares.

  Finally, let $r = product p_nu^(a_nu)$ be any positive rational integer, where
  the ${p_nu}$ #source(240)are primes, and let
  $
    p_nu = nr m_nu, quad
    m_nu in bold(Z) plus.o bold(Z) i plus.o bold(Z) j plus.o bold(Z) k.
  $
  Then
  $
    r = product p_nu^(a_nu) = product nr (m_nu^(a_nu))
    = nr product m_nu^(a_nu).
  $
  This proves that $r$ is a sum of four squares of rational integers, and the
  theorem is established.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $R = bold(Z)$ or $R = k[X]$, where $card k = q$. For nonzero $alpha in R$,
  let $abs(alpha) = card R slash R alpha$, and set $abs(0) = 0$. Prove that
  $abs(alpha)$ is finite for all $alpha in R$, and
  + $abs(alpha beta) = abs(alpha) abs(beta)$,
    $abs(alpha + beta) <= abs(alpha) + abs(beta)$, $alpha, beta in R$.
  + For each positive integer $n$, the number of elements $alpha in R$ with
    $abs(alpha) <= n$ is finite, and is at least $n$.
    #hint[@exc:absolute-value-properties][Let $deg alpha$ denote the degree of a
      polynomial $alpha in k[X]$, with $deg 0 = -infinity$. Then
      $abs(alpha) = q^(deg alpha)$, which yields (i). Further, $abs(alpha) <= n$
      if and only if $deg alpha <= log_q n$. The number of such $alpha$'s equals
      $q^(1+r)$, where $r$ is the greatest integer such that
      $r <= log_q n$.] <hint:absolute-value-properties>
] <exc:absolute-value-properties>

#exercise[
  Keeping the above notation, let $N subset M$ be free $R$-modules, where
  $
    M = dsum_(i=1)^d R m_i, quad N = dsum_(j=1)^d R n_j, quad
    n_j = sum a_(i j) m_i, quad a_(i j) in R.
  $
  Prove that $card M slash N = abs(det(a_(i j)))$.
  #hint[@exc:index-determinant][$R$ is a principal ideal domain. After basis
    changes in $M$ and $N$, which leave $abs(det(a_(i j)))$ unchanged, we may
    assume that $(a_(i j)) = diag(b_1, dots, b_d)$. Then
    $
      card M slash N = product card R slash R b_i = product abs(b_i)
      = abs(det(a_(i j))).
    $
    Compare with Exercise~@exc:order-ideal-determinant.]
  <hint:index-determinant>
] <exc:index-determinant>

#exercise[
  Keep the above notation, and let $Lambda$ be an $R$-order in a $K$-algebra
  $A$. Then for each $x in Lambda$ such that $x in u(A)$, we have
  $
    card Lambda slash Lambda x = abs(N_(A slash K) x),
  $
  where in this case the norm $N_(A slash K)$ must be computed by letting $x$
  act by right multiplication on an $R$-basis of $Lambda$.
] <exc:index-norm>

#exercise[
  Let $L$ be a finite separable extension of $K$, and let $R'$ be the integral
  closure of $R$ in $L$. Show that if $J Z(Lambda)$ holds for $R$-orders
  $Lambda$ in semisimple $K$-algebras, then $J Z(Lambda')$ holds for $R'$-orders
  $Lambda'$ in semisimple $L$-algebras.
  #hint[@exc:jordan-zassenhaus-extension][Since $R'$ is a finitely generated
    $R$-module, each such $Lambda'$ is also an $R$-order. Further, for each
    $Lambda'$-lattice $M$,
    $
      rank_R M = (L : K) dot rank_(R') M.
    $] <hint:jordan-zassenhaus-extension>
] <exc:jordan-zassenhaus-extension>

#exercise[
  Let $R' = S^(-1) R$ be a ring of quotients of $R$. Show that if $J Z$ holds
  for $R$-orders (in semisimple $K$-algebras), then $J Z$ also holds true for
  $R'$-orders. #hint[@exc:jordan-zassenhaus-quotients][Let the $R'$-order
    $Lambda'$ have $R'$-generators ${x_i}$, and let
    $x_i x_j = sum alpha_(i j l) x_l$, $alpha$'s in $R'$. Choose $s in S$ so
    #source(241)that each $s alpha_(i j l) in R$, and set
    $Lambda = R + sum R(s x_i)$. Then $Lambda$ is an $R$-order such that
    $R' Lambda = Lambda'$. Likewise, if $M' = sum Lambda' m_i$ is a
    $Lambda'$-lattice, then $M = sum Lambda m_i$ is a $Lambda$-lattice such that
    $Lambda' M = M'$, and $rank_R M = rank_(R') M'$. Deduce that if
    $J Z(Lambda)$ holds, then so does $J Z(Lambda')$. See also
    Exercise~@exc:lattice-generating-localization.]
  <hint:jordan-zassenhaus-quotients>
] <exc:jordan-zassenhaus-quotients>

#exercise[
  Let $A = bold(Q) plus.o bold(Q) v$, where $v^2 = 0$, and let
  $Lambda = bold(Z) plus.o bold(Z) v$ be a $bold(Z)$-order in $A$. For $r >= 1$,
  let $M_r$ be the unital $Lambda$-lattice $bold(Z) dotplus bold(Z)$, where
  $
    v(a, b) = (0, r a), quad (a, b) in M_r.
  $
  Show that if $M_r tilde.equiv M_s$, then $r = s$. (Consider
  $M_r slash v M_r$.) Thus $J Z(Lambda)$ cannot hold in this case.
] <exc:jordan-zassenhaus-fails>

#exercise[
  Suppose that $J Z(Lambda)$ holds true for the $R$-order $Lambda$ in the
  semisimple $K$-algebra $A$, and let $h(Lambda)$ be the number of classes of
  left $Lambda$-ideals $M$ in $A$ such that $K M = A$. Prove
  + If $Lambda subset Lambda' = R$-order, then $h(Lambda) >= h(Lambda')$.
  + If $Lambda$ and $Lambda'$ are maximal orders, then $h(Lambda) = h(Lambda')$.
  + If $Lambda$ is maximal, then $h(Lambda)$ equals the number of classes of
    right $Lambda$-ideals in $A$.
  + $h(Lambda') <= h(Lambda)$ if $Lambda'$ is a localization or completion of
    $Lambda$ at a prime ideal of $R$.
] <exc:class-number-properties>

#exercise[
  Let $Lambda$ be a maximal $R$-order in a separable $K$-algebra $A$. For
  $x in u(A)$, we call the maximal order $x Lambda x^(-1)$ _conjugate_#idx(
    "conjugate orders",
  ) to $Lambda$. Show that if $J Z(Lambda)$ holds true, then there are finitely
  many conjugacy classes of maximal $R$-orders in $A$.
] <exc:conjugate-maximal-orders>

#exercise[
  Let $L = bold(Q)(sqrt(2))$, $R = bold(Z)[sqrt(2)]$, $S = bold(Z)[2 sqrt(2)]$.
  Show that $R = algint {L}$, and that $R, S$ are $bold(Z)$-orders in $L$. Prove
  that $h(S) > h(R) = 1$. #hint[@exc:class-number-nonmaximal-order][$h(R) = 1$
    since $R$ has a euclidean algorithm (see
    Exercise~@exc:cyclic-algebra-sqrt2). Show that the ideal $2 S + 2 sqrt(2) S$
    is _not_ a principal ideal of $S$, so
    $h(S) >= 2$.] <hint:class-number-nonmaximal-order>
] <exc:class-number-nonmaximal-order>
