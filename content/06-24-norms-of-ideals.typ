#import "main-defs.typ": *
#import "statements.typ": *

== Norms of ideals <sec:norms-of-ideals>

Throughout this section let $A$ be a separable $K$-algebra. As in the preceding
sections, $M_(12)$ denotes an ideal in $A$ with left order $Lambda_1$ and right
order $Lambda_2$. We shall define norms and reduced norms of normal ideals of
$A$, so as to generalize the concept of relative norm in algebraic number theory
described in @rem:ramification-comments[(iii)]. To begin with, let $M = M_(12)$
be an integral ideal of $A$, and define its _norm_ by
#idx("norm (of ideal)")
$
  N_(A slash K) (M_(12)) = ord_R Lambda_1 slash M_(12).
$ <eq:norm-integral-ideal>
When there is no danger of confusion, we shall omit the subscripts $A slash K$
and $R$. Since $M_(12)$ is a full $R$-lattice in its left order $Lambda_1$, the
quotient $Lambda_1 slash M_(12)$ is a finitely generated torsion $R$-module.
Thus $ord Lambda_1 slash M$ is a nonzero ideal of $R$, and equals $R$ if and
only if $M = Lambda_1$.

We shall soon remove the asymmetry in the definition of norm, and we begin with
some easy results.

#theorem[
  + Let $M$ be an integral ideal of $A$. Then
    $
      N(M_P) = {N(M)}_P
    $
    for each prime ideal $P$ of $R$.
  + For each maximal $R$-order $Lambda$ in $A$,
    $
      N(Lambda a) = R dot N a = N(a Lambda), quad a in Lambda inter u(A).
    $
] <th:norm-local-principal>

#proof[
  (i) Let $Lambda = O_l (M)$, so $Lambda_P = O_l (M_P)$ by
  @eq:right-order-local. Therefore
  $
    N(M_P) = ord_(R_P) Lambda_P slash M_P = R_P times.o_R ord_R Lambda slash M
    = {N(M)}_P,
  $
  using @th:localization-dedekind[(ii)].

  (ii) We have
  $
    N(Lambda a) = ord Lambda slash Lambda a = R dot N a,
  $
  by Exercise~@exc:order-ideal-norm. In order to compute $N(a Lambda)$, we set
  $
    Lambda' = O_l (a Lambda) = a Lambda a^(-1).
  $
  Then
  $
    N(a Lambda) = ord Lambda' slash a Lambda
    = ord a Lambda a^(-1) slash a Lambda.
  $
  However, there is an $R$-isomorphism
  $
    a Lambda a^(-1) slash a Lambda tilde.equiv Lambda slash Lambda a, quad
    "given by" quad lambda -> a^(-1) lambda a, quad lambda in a Lambda a^(-1).
  $
  #source(220)Thus by Exercise~@exc:order-ideal-norm,
  $
    ord Lambda' slash a Lambda = ord Lambda slash Lambda a = R dot N a.
  $
  This completes the proof.
]

Using this result, we obtain a number of important consequences.

#theorem[
  Let $M_(12)$ be an integral ideal of $A$. Then
  $
    ord_R Lambda_1 slash M_(12) = ord_R Lambda_2 slash M_(12),
  $
  so that the norm of $M$ can be computed by using either the left order of $M$
  or the right order of $M$.
] <th:norm-left-right-orders>

#proof[
  In order to prove the equality of a pair of order ideals, it suffices to
  establish the equality after replacing $R$ by each of its localizations $R_P$,
  with $P$ an arbitrary prime ideal of $R$ (see
  Exercise~@exc:submodules-equal-locally). Changing notation, assume now that
  $R$ is a discrete valuation ring. By @th:separable-maximal-principal we may
  write $M = Lambda_1 a$ for some $a in u(A)$, and then
  $Lambda_2 = O_r (M) = a^(-1) Lambda_1 a$. The formula, which we are trying to
  prove, thus becomes
  $
    ord Lambda_1 slash Lambda_1 a = ord a^(-1) Lambda_1 a slash Lambda_1 a.
  $
  But we have already established this result in the proof of
  @th:norm-local-principal, and so the theorem is proved.
]

#theorem[
  Let $L dot M$ be a proper product of integral ideals. Then
  $
    N(L dot M) = N(L) dot N(M).
  $
] <th:norm-proper-product>

#proof[
  Let $L = L_(12)$, $M = M_(23)$. By @th:order-ideal-multiplicative, the exact
  sequence of left $Lambda_1$-modules
  $
    0 -> L slash L M -> Lambda_1 slash L M -> Lambda_1 slash L -> 0
  $
  gives rise to the equality
  $
    N(L M) = N(L) dot ord L slash L M.
  $
  Thus it suffices to show that $ord L slash L M = N(M)$. As in the proof of
  @th:norm-local-principal, it is enough to prove this when $R$ is a discrete
  valuation ring. But then $L = x Lambda_2$ for some $x in u(A)$, and so
  $
    L slash L M = x Lambda_2 slash x M tilde.equiv Lambda_2 slash M,
  $
  where the indicated isomorphism is an $R$-isomorphism. This implies at once
  that $ord L slash L M = N(M)$, and the theorem is proved.
]

We are now in a position to extend our definition of norm from integral #source(
  221,
)ideals to normal ideals. For each normal ideal $J$, choose a nonzero
$alpha in R$ such that $alpha J$ is integral, and let
$
  N^* (J) = alpha^(-n) N(alpha J), quad "where" quad n = (A : K).
$
Let us show at once that $N^* (J)$ does not depend on the choice of $alpha$. If
also $beta J subset Lambda = O_l (J)$, then
$
  alpha beta J = alpha Lambda dot beta J = beta Lambda dot alpha J,
$
and both of the indicated products are proper products. Hence
$
  N(alpha Lambda) N(beta J) = N(beta Lambda) N(alpha J)
$
by @th:norm-proper-product. But $N(alpha Lambda) = R dot alpha^n$,
$N(beta Lambda) = R dot beta^n$, whence
$
  alpha^(-n) N(alpha J) = beta^(-n) N(beta J),
$
as claimed. In particular, if $J$ is an integral ideal, we may choose
$alpha = 1$, and thus $N^* (J) = N(J)$.

#theorem[
  The above-defined norm $N^*$ satisfies
  $
    N^* (J dot J') = N^* (J) dot N^* (J')
  $
  for each proper product $J dot J'$ of normal ideals. Further
  $
    N^* (J^(-1)) = N^* (J)^(-1).
  $
] <th:norm-normal-ideals-multiplicative>

#proof[
  Choose a nonzero $alpha in R$ such that both $alpha J$ and $alpha J'$ are
  integral. Then $alpha J dot alpha J'$ is a proper product of integral ideals,
  and so
  $
    N(alpha J) N(alpha J') = N(alpha^2 J J') = alpha^(2n) N^* (J J').
  $
  This implies at once that $N^* (J J') = N^* (J) N^* (J')$. Further, if
  $Lambda = O_l (J)$ then $J dot J^(-1) = Lambda$, whence
  $
    R = N(Lambda) = N^* (J) dot N^* (J^(-1)).
  $
  This completes the proof of the theorem.
]

Hereafter we shall write $N$ instead of $N^*$, so we have now defined the norm
$N(J)$ of each normal ideal $J$ of $A$. If $J_1$ is a two-sided $Lambda_1$-ideal
in $A$, where $Lambda_1$ is a maximal order, then for each normal ideal
$L = L_(12)$, the proper product $L^(-1) J_1 L$ is a two-sided $Lambda_2$-ideal
$J_2$. We have called $J_1$ and $J_2$ _similar_ (see §~@sec:ideal-theory). It
follows at once that
$
  N(J_2) = N(L^(-1) J_1 L) = N(J_1),
$
so similar ideals have the same norm.

Let $frak(P)$ be any prime ideal of the maximal order $Lambda$, and set
$P = R inter frak(P)$, $overline(R) = R slash P$. We define the _inertial
degree_ of $frak(P)$ as #idx("inertial degree")
#source(222)
$
  f = f(frak(P), Lambda slash R) = (Lambda slash frak(P) : overline(R)).
$
Since $Lambda slash frak(P) tilde.equiv overline(R)^((f))$ as $R$-modules, we
obtain
$
  N(frak(P)) = ord_R Lambda slash frak(P) = P^f.
$ <eq:norm-prime-ideal>
Define the _capacity_ $kappa$ of $frak(P)$ by the condition #idx("capacity")
$
  Lambda slash frak(P) tilde.equiv M_kappa (S), quad S = "skewfield".
$

#theorem[
  Similar prime ideals have the same inertial degree, capacity, and norm.
] <th:similar-primes-invariants>

#proof[
  Let $frak(P)_1$ be a prime ideal of the maximal order $Lambda_1$, and let
  $frak(P)_2 = L^(-1) frak(P)_1 L$ be a similar prime ideal in $Lambda_2$, where
  $L = L_(12)$ is a normal ideal. Clearly
  $frak(P)_1 inter R = frak(P)_2 inter R = P$, and by the proof of
  @th:prime-ideals-of-maximal-order we have
  $
    Lambda_i slash frak(P)_i tilde.equiv (Lambda_i)_P slash (frak(P)_i)_P,
    quad i = 1, 2.
  $
  To prove the theorem, it suffices to show that there is an isomorphism of
  $R slash P$-algebras
  $Lambda_1 slash frak(P)_1 tilde.equiv Lambda_2 slash frak(P)_2$, under the
  assumption that $R$ is a discrete valuation ring. But in this case,
  $L = Lambda_1 x$ for some $x in u(A)$, so
  $
    Lambda_2 slash frak(P)_2 = x^(-1) Lambda_1 x slash x^(-1) frak(P)_1 x
    tilde.equiv Lambda_1 slash frak(P)_1.
  $
  This completes the proof.
]

#corollary[
  Let $M$ be a maximal integral ideal, belonging to a prime ideal of inertial
  degree $f$ and capacity $kappa$. Then
  $
    N(M) = P^(f slash kappa), quad "where" quad P = R inter M.
  $
] <cor:norm-maximal-integral-ideal>

#proof[
  Let $Lambda = O_l (M)$, and let $M$ belong to the prime ideal $frak(P)$ of
  $Lambda$. Then $Lambda slash frak(P) tilde.equiv (Lambda slash M)^((kappa))$
  as left $Lambda$-modules, whence
  $
    P^f = N(frak(P)) = ord_R Lambda slash frak(P) = {ord_R Lambda slash M}^kappa
    = N(M)^kappa.
  $
  This proves the corollary. It should be pointed out that if
  $Lambda' = O_r (M)$, then $M$ also belongs to a prime ideal $frak(P)'$ of
  $Lambda'$. However, $frak(P)$ and $frak(P)'$ are similar by
  @cor:maximal-integral-ideal-similar-primes, and they have the same $P$, $f$,
  $kappa$ by @th:similar-primes-invariants, so the assertion of the corollary
  holds equally well when we work with $frak(P)'$ rather than $frak(P)$.
]

We shall next give another interpretation of norms, which relates norms of
ideals with norms of elements.

#theorem[
  Let $J$ be a normal ideal of $A$, and let $N$ denote $N_(A slash K)$. Then
  $
    N(J) = R"-ideal generated by" {N(x) : x in J}.
  $
] <th:norm-generated-by-element-norms>

#proof[
  #source(223)It suffices to prove the result when $R$ is a discrete valuation
  ring, and an obvious argument shows that we may restrict ourselves to the case
  where $J$ is an integral ideal. Then $J = Lambda a$ for some $a in u(A)$,
  where $Lambda = O_l (J)$, and so $N(J) = R dot N a$ by
  Exercise~@exc:order-ideal-norm. On the other hand,
  $
    sum_(x in J) R dot N(x) = sum_(lambda in Lambda) R dot N(lambda) N(a)
    = R dot N(a),
  $
  since $N(lambda) in R$ for each $lambda in Lambda$. This completes the proof.
]

#corollary[
  Let $K$ be a finite separable extension of the field $E$, and let $R$ be the
  integral closure in $K$ of the Dedekind domain $S$ with quotient field $E$.
  Then
  $
    N_(K slash E) (N_(A slash K) J) = N_(A slash E) J
  $
  for each normal ideal $J$ of $A$.
] <cor:norm-transitivity>

#proof[
  Let $J$ be a normal ideal of $A$, and set $Lambda = O_l (J)$. Then $Lambda$ is
  a maximal $S$-order in $A$, as well as a maximal $R$-order in $A$. To prove
  the stated equality of $S$-ideals in $E$, we need only prove the result when
  $S$ is replaced by its localizations at prime ideals of $S$. Changing
  notation, we assume that $S$ is a discrete valuation ring. Then $J = Lambda x$
  for some $x in u(A)$, and so
  $
    N_(A slash E) J = S dot N_(A slash E) x, quad
    N_(A slash K) J = R dot N_(A slash K) x.
  $
  But by @th:norm-local-principal, for each nonzero $alpha in R$ we have
  $
    N_(K slash E) (R alpha) = S dot N_(K slash E) alpha.
  $
  Therefore
  $
    N_(K slash E) (N_(A slash K) J) = S dot N_(K slash E) (N_(A slash K) x)
    = S dot N_(A slash E) x
  $
  by Exercise~@exc:transitivity-trace-norm. This completes the proof.
]

We shall now define reduced norms of normal ideals, and in order to avoid
cumbersome notation, we shall restrict our attention to the central simple case.
For the remainder of this section, let $A$ denote a central simple $K$-algebra,
and let $(A : K) = n^2$ hereafter. Denote by "nr" the reduced norm map
$nr : A -> K$, so by @eq:trace-norm-reduced-powers we have
$
  N_(A slash K) a = (nr a)^n, quad a in A.
$

#theorem[
  For each normal ideal $J$ in the central simple $K$-algebra $A$, the norm
  $N(J)$ is the $n$-th power of an $R$-ideal $nr J$, called the _reduced norm_
  of $J$. For each proper product $J dot J'$ of normal ideals in $A$, we have
  #idx("reduced norm of ideal")#idx("norm (reduced, of ideal)")
  $
    nr (J dot J') = (nr J)(nr J').
  $
] <th:reduced-norm-of-ideal>

#proof[
  #source(224)To prove that $N(J)$ is an $n$th power, it suffices to show that
  for each prime ideal $P$ of $R$, $N(J_P)$ is an $n$th power. Changing
  notation, we may assume that $R$ is a discrete valuation ring. But then
  $J = Lambda a$ for some $a in u(A)$, where $Lambda = O_l (J)$, and thus
  $
    N(J) = R dot N_(A slash K) a = (R dot nr a)^n.
  $
  Finally, $N$ is multiplicative on proper products by
  @th:norm-normal-ideals-multiplicative, whence so is "nr". This completes the
  proof.
]

As a direct consequence of @th:norm-generated-by-element-norms and
@th:reduced-norm-of-ideal, we obtain

#corollary[
  For each normal ideal $J$ in $A$, $nr J = R$-ideal generated by
  ${nr x : x in J}$.
] <cor:reduced-norm-generated>

We shall now establish the following important result:

#theorem(major: true)[
  Let $M$ be a maximal integral ideal of the central simple $K$-algebra $A$, and
  set $P = M inter R$, $overline(R) = R slash P$. If $overline(R)$ is a finite
  field, then
  $
    nr M = P, quad N(M) = P^n, quad (A : K) = n^2.
  $
] <th:reduced-norm-maximal-ideal>

#proof[
  Let $Lambda = O_l (M)$, and let $frak(P)$ be the prime ideal of $Lambda$ to
  which $M$ belongs. By @cor:norm-maximal-integral-ideal
  $
    nr M = P^(f slash kappa n),
  $
  where $f$ is the inertial degree of $frak(P)$ and $kappa$ is the capacity of
  $frak(P)$. Letting $hat(R)$ denote the $P$-adic completion of $R$, we have
  $
    hat(Lambda) slash hat(frak(P)) tilde.equiv Lambda_P slash frak(P)_P
    tilde.equiv Lambda slash frak(P)
  $
  by @th:local-completion-comparison and @th:prime-ideals-of-maximal-order.
  Further, $hat(A)$ is a central simple $hat(K)$-algebra and
  $(hat(A) : hat(K)) = (A : K) = n^2$. Thus we can compute $f$, $kappa$, $n$ by
  working with the case where the underlying ring is $hat(R)$, rather than $R$.

  Let us write $hat(A) tilde.equiv M_r (D)$, where $D$ is a skewfield with
  center $hat(K)$ and index $m$. Then $hat(Lambda) tilde.equiv M_r (Delta)$,
  where $Delta$ is the maximal $hat(R)$-order in $D$, and we have
  $
    hat(Lambda) slash hat(frak(P)) tilde.equiv M_r (Delta slash rad Delta).
  $
  Further, $Delta slash rad Delta$ is a skewfield of dimension $m$ over
  $overline(R)$, by @th:local-skewfield-e-f. Hence we obtain
  $
    f = (hat(Lambda) slash hat(frak(P)) : overline(R)) = r^2 m, quad
    kappa = r, quad n^2 = (hat(A) : hat(K)) = r^2 m^2.
  $
  This gives
  $
    f slash kappa n = r^2 m slash r dot r m = 1,
  $
  and completes the proof.
]

#corollary(major: true)[
  #source(225)Let $M$ be an integral ideal of the central simple $K$-algebra
  $A$, and assume that $R slash P$ is finite for each maximal ideal $P$ of $R$.
  Then $nr M$ is the product of the $R$-annihilators of the $Lambda$-composition
  factors of the left $Lambda$-module $Lambda slash M$, where
  $Lambda = O_l (M)$.
] <cor:reduced-norm-composition-factors>

#proof[
  Let ${S_i}$ be the set of $Lambda$-composition factors of $Lambda slash M$,
  and write $S_i tilde.equiv Lambda slash M_i$, with $M_i$ a maximal left ideal
  of $Lambda$. Then $ann_R S_i = M_i inter R = P_i$ (say), and $N(M_i) = P_i^n$
  by @th:reduced-norm-maximal-ideal. Hence by @th:order-ideal-multiplicative we
  have
  $
    N(M) = ord_R Lambda slash M = product ord_R S_i = product N(M_i)
    = (product P_i)^n.
  $
  Since $N(M) = (nr M)^n$, we obtain $nr M = product P_i$, as desired.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

In Exercises~@exc:norm-completion–@exc:counting-norm, $A$ is a separable
$K$-algebra, $M$ is a normal ideal in $A$, and $Lambda = O_l (M)$.

#exercise[
  Let $hat(R)$ be the $P$-adic completion of $R$, where $P$ is a prime ideal of
  $R$. Show that $hat(R) times.o_R N(M) = N(hat(M))$.
  #hint[@exc:norm-completion][It suffices to prove the result when $M$ is
    integral. But
    $
      hat(R) times.o_R ord_R Lambda slash M
      = ord_(hat(R)) hat(Lambda) slash hat(M)
    $
    by Exercise~@exc:order-ideal-extension.] <hint:norm-completion>
] <exc:norm-completion>

#exercise[
  If $M$ is integral, prove that
  $
    ord_R Lambda slash M = ord_R M^(-1) slash Lambda.
  $
  #hint[@exc:norm-inverse-ideal][After localizing, write $M = Lambda x$. Then
    $
      M^(-1) slash Lambda = x^(-1) Lambda slash Lambda
      tilde.equiv Lambda slash Lambda x.
    $
    Now use @th:norm-local-principal.] <hint:norm-inverse-ideal>
] <exc:norm-inverse-ideal>

#exercise[
  Let $M$ be integral, and let $K = bold(Q)$, $R = bold(Z)$. Prove that
  $
    N(M) = (card Lambda slash M) dot bold(Z).
  $
  Call $card Lambda slash M$ the _counting norm_ or _absolute norm_ of $M$.
  #idx("counting norm")#idx("norm (counting)")
] <exc:counting-norm>

#exercise[
  Let $Lambda$ be a maximal order in a central simple $K$-algebra $A$, and let
  $J$ be a proper two-sided ideal of $Lambda$. Define a _$J$-adic valuation_ $w$
  on $A$ as follows: for $a in A$, $a != 0$, let $w(a)$ be the least integer
  such that #idx("valuation ($J$-adic)")
  $
    Lambda dot a dot Lambda = J^(w(a)) B C^(-1),
  $
  where $B$ and $C$ are two-sided ideals of $Lambda$ such that $B + C = Lambda$
  and $J$ does not divide $B$. Set $w(0) = +infinity$. Prove that
  $
    w(a + b) >= min (w(a), w(b)), quad w(a b) >= w(a) + w(b), quad a, b in A.
  $

  Now give $A$ the $J$-adic topology, in which two elements $a, b in A$ are near
  each other if $w(a - b)$ is large. Let $hat(A)_J$ denote the $J$-adic
  completion of $A$, and $hat(Lambda)_J$ the completion of $Lambda$. Show that
  each element of $hat(Lambda)_J$ is representable by a sequence ${a_n}$ from
  $Lambda$, with
  #source(226)
  $
    a_(n+1) equiv a_n (mod J^n), quad n = 1, 2, dots .
  $

  Let $J = product_(i=1)^r frak(P)_i^(e_i)$, where the ${frak(P)_i}$ are
  distinct prime ideals of $Lambda$, and each $e_i >= 1$. Using
  Exercise~@exc:prime-power-products[(iv)], show that
  $
    hat(Lambda)_J tilde.equiv dsum_(i=1)^r hat(Lambda)_(frak(P)_i).
  $
  Prove further that if $P_i = R inter frak(P)_i$, then
  $
    hat(Lambda)_(frak(P)_i) tilde.equiv hat(Lambda)_(P_i)
    tilde.equiv hat(R)_(P_i) times.o_R Lambda.
  $
  Calculate the completion $hat(Lambda)_(frak(a) Lambda)$, where $frak(a)$ is
  any ideal of $R$.
] <exc:j-adic-valuation>

#exercise[
  Let $Lambda$ be a maximal order in a central simple $K$-algebra $A$, and let
  $M$ be a left ideal in $Lambda$, and $J$ a two-sided ideal in $Lambda$. Call
  $M$ and $J$ _relatively prime_ if $M + J = Lambda$. Prove that the following
  are equivalent: #idx("relatively prime (ideals)")
  + $M$ and $J$ are relatively prime.
  + For each prime $frak(P)$ of $Lambda$ dividing $J$,
    $hat(M)_(frak(P)) = hat(Lambda)_(frak(P))$.
  + For each prime $P$ of $R$, either $J_P = Lambda_P$ or $M_P = Lambda_P$.
  + $N_(A slash K) M + N_(A slash K) J = R$.
  (See also Exercise~@exc:relatively-prime-norms.)
] <exc:relatively-prime-ideals>
