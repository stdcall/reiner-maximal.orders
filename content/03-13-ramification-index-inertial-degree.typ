#import "main-defs.typ": *
#import "statements.typ": *

== Ramification index, inertial degree <sec:ramification-index-inertial-degree>

Keeping the notation of §~@sec:uniqueness-of-maximal-orders, let $D$ be a
skewfield of finite dimension over a complete $P$-adic field $K$ contained in
the center of $D$, and let $Delta$ be the unique maximal $R$-order in $D$. We
shall define the _ramification index_ $e = e(D slash K)$ and _inertial degree_
$f = f(D slash K)$, and shall show that the analogue of
@th:extensions-complete-fields[Theorem] holds true in this case. In fact, the
discussion below does not make use of any of the earlier results from
§~@sec:completions-and-valuations, and so provides a proof of
@th:extensions-complete-fields[Theorem], by choosing $D$ to be a field.

Let $v$ be the exponential valuation on $K$, and let $w$ be the extension of $v$
to the skewfield $D$. We have seen that the value group of $v$ is $bold(Z)$,
while the value #source(148)group of $w$ is a subgroup of $m^(-1) bold(Z)$,
where $m = (D : K)$. Hence the value group of $w$ equals $e^(-1) bold(Z)$, for
some positive integer $e$ dividing $m$. We write $e = e(D slash K)$, and call
$e$ the _ramification index_#idx("ramification index") of $D$ over $K$. Thus,
the least positive number in the set ${w(a) : a in Delta}$ is precisely
$1 slash e$.

We shall now _normalize_#idx("normalized valuation") the valuation $w$, by
replacing $w$ by the equivalent valuation $v_D$, where $v_D = e dot w$. Then
$v_D$ has value group $bold(Z)$, and for $a in D$,
$
  cases(
    v_D (a) & = (e slash m) dot v(N_(D slash K) a),
    & = e dot (K(a) : K)^(-1) v(f(0))"," quad "where" quad
      f(X) = minpol_K a.,
  )
$ <eq:normalized-skewfield-valuation>
Let $pi in R$ be a prime element, so $v(pi) = 1$. We may choose $pi_D in Delta$
so that $v_D (pi_D) = 1$; call $pi_D$ a _prime element_#idx("prime element") of
$Delta$. We have at once
$
  v_D (pi) = e.
$
The group of units of $Delta$ is given by
$
  u(Delta) = {a in Delta : v_D (a) = 0}
  = {a in Delta : N_(D slash K) a in u(R)}.
$
Each nonzero $a in D$ is uniquely expressible as
$
  a = pi_D^n dot a' = a'' dot pi_D^n, quad n = v_D (a), quad "where" quad
  a', a'' in u(Delta).
$
Note that $a'$ and $a''$ need not be equal.

#theorem[
  Let $pi_D$ be a prime element of $Delta$, and set $frak(p) = pi_D Delta$. Then
  every nonzero one-sided ideal of $Delta$ is a two-sided ideal, and is a power
  of $frak(p)$. The residue class ring $Delta slash frak(p)$ is a skewfield over
  the field $overline(R)$, and $frak(p) inter R = P$.
] <th:skewfield-order-ideals>

#proof[
  For $L$ any nonzero left ideal in $Delta$, let
  $
    l = min {v_D (a) : a in L},
  $
  and choose an element $x in L$ such that $v_D (x) = l$. Then for each $y in L$
  we have $y x^(-1) in Delta$, so $y in Delta x subset L$. This proves that
  $L = Delta x$. Furthermore, $Delta x = x Delta$ since
  $
    v_D (x^(-1) a x) = v_D (a), quad a in D.
  $
  Thus $L$ is a two-sided ideal of $Delta$, and clearly
  $
    L = pi_D^l Delta = Delta pi_D^l = frak(p)^l, quad "since" quad
    x dot pi_D^(-l) in Delta.
  $

  The above shows that $frak(p)$ is a maximal left ideal of $Delta$. The ring
  $overline(Delta) = Delta slash frak(p)$ therefore has no left ideals except 0
  and $overline(Delta)$, and thus $overline(Delta)$ is a skewfield. Finally,
  $frak(p) inter R$ is a prime ideal of $R$, and is nonzero since $frak(p)$ is a
  full $R$-lattice in $D$. Thus $frak(p) inter R = P$, whence
  $P dot overline(Delta) = 0$, so $overline(Delta)$ is a skewfield over
  $overline(R)$.
]

#source(149)We now define the _inertial degree_ of $D$ over $K$ as
#idx("inertial degree")
$
  f = f(D slash K) = (overline(Delta) : overline(R)).
$
Note that $overline(Delta) = Delta slash frak(p)$ is a vector space over
$overline(R)$, since $P subset frak(p)$. The fact that $f$ is finite follows
from the theorem below, which generalizes
@th:extensions-complete-fields[Theorem], and indeed provides an independent
proof thereof.

#theorem[
  Let $D$ be a skewfield of finite dimension $m$ over a complete $P$-adic field
  $K$ contained in the center of $D$. Let $e = e(D slash K)$ be the ramification
  index of $D$ over $K$, and $f = f(D slash K)$ the inertial degree of $D$ over
  $K$. Both $e$ and $f$ are finite, and
  $
    e dot f = (D : K) = m.
  $
  Let $a_1, dots, a_f in Delta$ be such that
  $overline(Delta) = dsum overline(R) overline(a)_i$, and let
  $b_0, dots, b_(e-1) in Delta$ be such that $v_D (b_j) = j$, $0 <= j <= e - 1$.
  Then the $e dot f$ products ${a_i b_j}$ form a free $R$-basis for $Delta$.
] <th:skewfield-ef>

#proof[
  First, let ${a_i : 1 <= i <= s}$ be elements in $Delta$ whose images
  ${overline(a)_i}$ in $overline(Delta)$ are linearly independent over
  $overline(R)$, and let ${b_j : 1 <= j <= t}$ be elements of $D$ such that the
  integers ${v_D (b_j)}$ are incongruent $mod e$. We claim that the $s dot t$
  products ${a_i b_j}$ are linearly independent over $K$. If not, there is a
  relation
  $
    (sum alpha_(1 i) a_i) b_1 + dots.c + (sum alpha_(t i) a_i) b_t = 0, quad
    alpha_(j i) in K,
  $ <eq:skewfield-ef-relation>
  where we may assume that for each $b_j$, at least one of the coefficients
  $alpha_(j 1), dots, alpha_(j s)$ is nonzero. Write
  $
    n_j = min {v(alpha_(j i)) : 1 <= i <= s}, quad
    alpha_(j i) = pi^(n_j) dot beta_(j i).
  $
  Then each $beta_(j i) in R$, and for each $j$ there is an index $k$ for which
  $beta_(j k) in.not P$. We may rewrite @eq:skewfield-ef-relation as
  $
    (sum beta_(1 i) a_i) pi^(n_1) b_1 + dots.c
    + (sum beta_(t i) a_i) pi^(n_t) b_t = 0.
  $
  Since $v_D (pi) = e$, replacing each $b_j$ by $pi^(n_j) b_j$ does not affect
  the hypotheses or the conclusion. After making this replacement, and
  renumbering the $a$'s and $b$'s if need be, we obtain a relation
  $
    (sum gamma_(1 i) a_i) b_1 + dots.c + (sum gamma_(t i) a_i) b_t = 0,
  $
  where each $gamma_(j i) in R$, and
  $
    v_D (b_1) < dots.c < v_D (b_t),
  $
  and $gamma_(11) in.not P$. Therefore
  $
    sum_j (sum_i gamma_(j i) a_i) b_j slash b_1 = 0, quad "and" quad
    b_j slash b_1 in frak(p) quad "for" quad 2 <= j <= t.
  $
  #source(150)Passing to the residue class ring $overline(Delta)$, we obtain the
  relation $sum overline(gamma)_(1 i) overline(a)_i = 0$, with
  $overline(gamma)_(11) != 0$, which contradicts the linear independence of the
  ${overline(a)_i}$ over $overline(R)$. We have therefore established that the
  $s dot t$ products ${a_i b_j}$ are elements of $D$ linearly independent over
  $K$, so $s t <= m$. This proves that $f$ is finite, and shows also that
  $e f <= m$.

  Now let $a_1, dots, a_f, b_0, dots, b_(e-1) in Delta$ be elements satisfying
  the hypotheses of the theorem. The $e dot f$ elements ${a_i b_j}$ are linearly
  independent over $K$, by the first part of the proof, and we need only show
  that $Delta = sum_(i, j) R a_i b_j$. Let $x in Delta$, $x != 0$, and let
  $v_D (x) = k e + j$, where $0 <= j <= e - 1$. Then
  $
    x = u (pi^k b_j), quad u in u(Delta).
  $
  Since the ${overline(a)_i}$ form an $overline(R)$-basis for $overline(Delta)$,
  we may find elements ${r_i}$ in $R$ such that
  $u = r_1 a_1 + dots.c + r_f a_f + z$, with $z in frak(p)$. Hence we have
  $
    x = (sum_i r_i pi^k a_i) b_j + x_1, quad "where" quad
    v_D (x_1) > v_D (x).
  $
  If $x_1 != 0$, we may repeat this procedure with $x_1$, and continue if need
  be with $x_2, x_3, dots$. Note that $k$ is the greatest integer in
  $v_D (x) slash e$. Hence after $n dot e$ steps, we obtain an equality
  $
    x = sum_(j=0)^(e-1) sum_(i=1)^f (r_(i j)^((1)) pi^k
      + r_(i j)^((2)) pi^(k+1) + dots.c + r_(i j)^((n)) pi^(k+n-1)) a_i b_j
    + y_n,
  $ <eq:skewfield-basis-approximation>
  where $v_D (y_n) >= v_D (x) + n e$.

  For fixed $i, j$, the sequence
  $
    r_(i j)^((1)) pi^k, quad r_(i j)^((1)) pi^k + r_(i j)^((2)) pi^(k+1),
    quad dots
  $
  is a Cauchy sequence from $R$, relative to the $P$-adic valuation of $R$.
  Since $R$ is assumed complete, this sequence has a limit $s_(i j) in R$. If we
  set $x' = sum_(i, j) s_(i j) a_i b_j in Delta$, then for each $n$ we have from
  @eq:skewfield-basis-approximation
  $
    v_D (x - x') >= min (v_D (y_n), k + n - 1).
  $
  Thus $v_D (x - x') = infinity$, so $x = x'$. Therefore $x in sum R a_i b_j$,
  and the theorem is proved.
]

We have now established that $Delta$ is finitely generated as $R$-module, and
indeed that $Delta$ is a free $R$-module on $m$ generators. This shows that
@th:skewfield-unique-maximal-order[Theorem] is valid, that is, $Delta$ is the
unique maximal $R$-order in $D$.

#corollary[
  The skewfield $D$ is complete relative to the valuation $v_D$.
] <cor:skewfield-complete>

#proof[
  #source(151)Keeping the notation of @th:skewfield-ef, we have
  $D = dsum_(i, j) K a_i b_j$. Let ${x_1, x_2, dots}$ be a Cauchy sequence from
  $D$, whence $v_D (x_n - x_(n-1)) -> infinity$ as $n -> infinity$. Write
  $
    x_n = sum_(i, j) r_(i j)^((n)) a_i b_j, quad r_(i j)^((n)) in K, quad
    n >= 1.
  $
  Set
  $
    v_D (x_n - x_(n-1)) = e dot k_n + l_n, quad 0 <= l_n <= e - 1,
  $
  so also $lim_(n -> infinity) k_n = infinity$. We have then
  $
    x_n - x_(n-1) = pi^(k_n) dot y_n, quad y_n in Delta.
  $
  Write $y_n$ as an $R$-linear combination of the ${a_i b_j}$; then by
  @th:skewfield-ef, it follows from the above equation that
  $
    r_(i j)^((n)) - r_(i j)^((n-1)) in pi^(k_n) R.
  $
  Hence ${r_(i j)^((1)), r_(i j)^((2)), dots}$ is a Cauchy sequence from $K$,
  with limit $rho_(i j)$, say. Then obviously
  $
    lim_(n -> infinity) x_n = sum_(i, j) rho_(i j) a_i b_j.
  $
]

#theorem[
  Let $K$ be the center of the skewfield $D$, and set $(D : K) = n^2$,
  $e = e(D slash K)$, $f = f(D slash K)$. Then
  $
    e f = n^2, quad e | n, quad n | f.
  $
] <th:skewfield-e-divides-index>

#proof[
  Let $w$ be the extension of $v$ to $D$ defined in @eq:skewfield-valuation. By
  definition of $e$, we have $w(pi_D) = 1 slash e$. Then $K(pi_D)$ is a subfield
  of $D$, and has ramification index $e$. Hence by
  @th:extensions-complete-fields or @th:skewfield-ef, we have
  $e | (K(pi_D) : K)$. But $K(pi_D)$ lies in some maximal subfield $E$ of $D$,
  whence $(K(pi_D) : K) | (E : K)$. Since $(E : K) = n$ by
  @th:maximal-subfields, the result follows.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $cal(S)$ be any full set of representatives in $Delta$ of the residue
  classes in $overline(Delta)$, where we assume that $0 in cal(S)$. Prove that
  every nonzero $x in D$ is uniquely expressible as
  $
    x = pi_D^(v_D (x)) dot (s_0 + s_1 pi_D + s_2 pi_D^2 + dots.c), quad
    s_i in cal(S), quad s_0 != 0.
  $
] <exc:skewfield-power-series>

#exercise[
  Prove that the order ideal $ord_R overline(Delta)$ equals $P^f$, where
  $f = f(D slash K)$. #hint[@exc:residue-skewfield-order-ideal][$overline(Delta)
    tilde.equiv overline(R)^((f))$ as $overline(R)$-modules.]
  <hint:residue-skewfield-order-ideal>
] <exc:residue-skewfield-order-ideal>

#exercise[
  Prove that $v(N_(D slash K) pi_D) = f$, and that
  $v(nr_(D slash K) pi_D) = sqrt(f slash e)$.
  #hint[@exc:norm-of-prime-element][$e^(-1) = m^(-1) v(N_(D slash K) pi_D)$,
    $m = (D : K)$, so $v(N_(D slash K) pi_D) = f$. Next,
    $
      N_(D slash K) pi_D = (nr pi_D)^(sqrt((D : K))), "so"
      f = sqrt((D : K)) v(nr pi_D) = sqrt(e f) dot v(nr pi_D).
    $] <hint:norm-of-prime-element>
] <exc:norm-of-prime-element>

#exercise[
  #source(152)A _fractional_#idx("fractional ideal")#idx("ideal", "fractional")
  $Delta$-ideal is a full left $Delta$-lattice in $D$. Show that the set of
  fractional $Delta$-ideals, with the obvious definition of multiplication, is
  an infinite cyclic group generated by the ideal $frak(p)$. Prove also that
  $frak(p) = rad Delta$.
] <exc:skewfield-fractional-ideals>
