#import "main-defs.typ": *
#import "statements.typ": *

== Reduced norms <sec:reduced-norms-global>

Throughout this section $K$ is assumed to be a global field, unless otherwise
stated. Let $nr_(A slash K): A -> K$ be the reduced norm map, where $A$ is a
central simple $K$-algebra, and let
$
  nr A = nr_(A slash K) (A) = {nr_(A slash K) a : a in A}.
$
Our aim is to determine the image $nr A$ explicitly.

Our first result, true for arbitrary fields $K$, enables us to reduce the
problem to the case where $A$ is a skewfield.

#theorem[
  Let $A = M_r (D)$, where $D$ is a skewfield with center $K$ (not necessarily a
  global field). Then
  + $nr_(A slash K) (A) = nr_(D slash K) (D)$.
  + For $a in A$, $nr_(A slash K) a = 0$ if and only if $a$ is a nonunit of $A$.
] <th:reduced-norm-matrix-ring>

#proof[
  We shall omit the subscripts $A slash K$ and $D slash K$ when there is no
  danger of confusion. As in Exercise~@exc:reduced-trace-matrix-ring, let $E$ be
  a splitting field for $D$, and let
  $
    mu: D -> E times.o_K D tilde.equiv M_s (E).
  $
  Then there is an embedding
  $
    A -> E times.o_K A tilde.equiv M_(r s) (E),
  $
  given by
  $
    a = (alpha_(i j))_(1 <= i, j <= r) in M_r (D) -> (mu(alpha_(i j)))
    in M_(r s) (E).
  $
  By definition of the reduced norm map, we have
  $
    nr a = det (mu(alpha_(i j))), quad a = (alpha_(i j)) in M_r (D).
  $
  In particular, if $a = (alpha_(i j))$ is an upper triangular matrix, then
  $
    nr a = product_(i=1)^r det (mu(alpha_(i i)))
    = product_(i=1)^r nr alpha_(i i),
  $ <eq:reduced-norm-triangular>
  where $nr alpha_(i i)$ means $nr_(D slash K) alpha_(i i)$. The same holds true
  if $a$ is lower triangular. #source(292)Finally, let $t in M_r (D)$ be any
  transposition matrix. From the identity
  $
    mat(0, 1; 1, 0) = mat(1, -1; 0, 1) mat(1, 0; 1, 1) mat(1, 1; 0, -1),
  $
  it follows at once that $nr t = nr_(D slash K) (-1)$.

  By an "elementary matrix" in $M_r (D)$ we shall mean a matrix $bolditalic(e)$
  which coincides with the $r times r$ identity matrix, except for having a
  single nonzero entry off the main diagonal. By @eq:reduced-norm-triangular,
  $nr bolditalic(e) = 1$. Given an arbitrary $a in A$, we can find matrices
  $p, q in A$ which are products of elementary matrices and transpositions, such
  that
  $
    p a q = diag(alpha_1, dots, alpha_r), quad alpha_i in D.
  $
  Note that $a in u(A)$ if and only if each $alpha_i in u(D)$.

  Since $nr_(A slash K)$ is multiplicative, and since $nr p$ and $nr q$ can only
  have the values $nr_(D slash K) (plus.minus 1)$, it follows that
  $
    nr a = nr (plus.minus alpha_1 dots.c alpha_r).
  $
  This implies (i) immediately. It also proves (ii), since
  $nr (plus.minus alpha_1 dots.c alpha_r) = 0$ if and only if some
  $alpha_i = 0$.
]

Let $P$ be a prime of $K$, and let the subscript $P$ indicate $P$-adic
completion. For any $K$-algebra $A$, the embedding
$
  A -> K_P times.o_K A = A_P
$
carries each $x in A$ onto an element $x_P$ of $A_P$. We have at once

#theorem[
  Let $A$ be a central simple $K$-algebra, and let $P$ be a prime of $K$. Then
  $
    nr_(A slash K) x = nr_(A_P slash K_P) x_P, quad x in A.
  $
] <th:reduced-norm-completion>

#proof[
  Use @eq:reduced-char-pol-ground-field, with $F$ replaced by $K_P$.
]

We call elements of $nr A$ _global_ reduced norms, and those of $nr A_P$ _local_
reduced norms. The above theorem tells us that every global reduced norm is also
a local reduced norm at each $P$. We shall eventually prove the converse, when
$K$ is a global field. As a first step, let us determine which elements are
local reduced norms.

#theorem(major: true)[
  Let $P$ be a prime of the global field $K$, and let $B$ be any central simple
  $K_P$-algebra. Then
  $
    nr_(B slash K_P) B = K_P,
  $
  except for the special case where $K_P = bold(R)$ and $B tilde.op bold(H)$. In
  that case,
  $
    nr B = nr bold(H) = bold(R)^+ = {alpha in bold(R) : alpha >= 0}.
  $
] <th:local-reduced-norms>

#proof[
  #source(293)By @th:reduced-norm-matrix-ring we may assume that $B$ is a
  skewfield $S$ with center $K_P$. If $P$ is a finite prime, then $nr S = K_P$
  by Exercise~@exc:reduced-norm-surjective. If $P$ is an infinite prime, then by
  @th:infinite-prime-local-index we have $S = K_P$ (and so also $nr S = K_P$),
  except for the special case where $K_P = bold(R)$, $S = bold(H)$. It remains
  for us to prove that $nr bold(H) = bold(R)^+$.

  Let $a = alpha_0 + alpha_1 i + alpha_2 j + alpha_3 k in bold(H)$,
  $alpha_nu in bold(R)$. Then (see @exm:quaternions) we have
  $
    nr_(bold(H) slash bold(R)) a
    = alpha_0^2 + alpha_1^2 + alpha_2^2 + alpha_3^2 in bold(R)^+.
  $
  Conversely, each $alpha in bold(R)^+$ is expressible in the form $alpha_0^2$,
  $alpha_0 in bold(R)$. This shows that $nr bold(H) = bold(R)^+$, and completes
  the proof.
]

Now let $A$ be a central simple $K$-algebra, where $K$ is a global field, and
let $P$ be a prime of $K$. For $alpha in K$, let $alpha_P$ denote its image in
$K_P$. By @th:reduced-norm-completion, we have
$
  alpha in nr A quad ==> quad alpha_P in nr A_P "for each" P.
$ <eq:global-reduced-norm-local>
If we are trying to decide whether a given element $alpha in K$ is a global
reduced norm, we must therefore first check whether $alpha$ is a local reduced
norm at each $P$. By @th:local-reduced-norms, the condition that
$alpha_P in nr A_P$ is automatically satisfied for every finite prime $P$, and
also for every infinite prime $P$ as well, except for the special case where
$K_P = bold(R)$ and $A_P tilde.op bold(H)$. This special case can only arise
when $P$ is a real prime which is _ramified_ in $A$, using the terminology
introduced in §~@sec:splitting-of-simple-algebras.

Given the central simple $K$-algebra $A$, we define
$
  U(A) = {alpha in K^* : alpha_P > 0 "at each real prime" P "of" K
    "ramified in" A}.
$ <eq:reduced-norm-positivity-set>
The preceding discussion then shows that for $alpha in K^*$,
$
  alpha_P in nr A_P quad "for all" P quad <==> quad alpha in U(A).
$ <eq:local-reduced-norm-criterion>
We intend to prove that $alpha in nr A$ if and only if $alpha in U(A)$, and we
begin with two preliminary lemmas which are of interest in themselves.

#lemma[
  Let $K$ be any field complete with respect to a valuation $|thin|$. Let
  $
    f(X) = X^n + a_1 X^(n-1) + dots.c + a_n in K[X]
  $
  be a separable irreducible polynomial. Set
  $
    L = K(xi), quad "where" quad minpol_K xi = f(X).
  $
  Then for any polynomial
  $
    g(X) = b_1 X^(n-1) + dots.c + b_n in K[X],
  $
  for which the values $abs(b_1), dots, abs(b_n)$ are sufficiently small, the
  polynomial $f(X) + g(X)$ is also irreducible and separable, and has a zero in
  $L$.
] <lem:perturbed-polynomial-irreducible>

#proof[
  _Step 1._ The result is obvious when $n = 1$, so assume that $n > 1$
  hereafter. Let us first settle the case where the valuation is archimedean, in
  #source(294)which case $K = bold(R)$ or $bold(C)$. Since $n > 1$, the only
  possibility is that $K = bold(R)$, $L = bold(C)$, and $f(X)$ is a quadratic
  polynomial with no real zeros. If the coefficients of $g(X)$ are sufficiently
  small, then also $f(X) + g(X)$ has no real zeros, so $f(X) + g(X)$ is
  irreducible in $K[X]$, and has a zero in $L$. Thus the result holds in this
  case.

  _Step 2._ (_Krasner's Lemma_). #idx("Krasner's Lemma")For the rest of the
  proof, we assume that the valuation is non-archimedean, and that $n > 1$. Let
  $tilde(K)$ be an algebraic closure of $K$ containing $L$, and extend $|thin|$
  to a valuation on $tilde(K)$ as in §~@ss:extensions-of-complete-fields. Two
  elements $gamma, gamma'$ in $tilde(K)$ are _conjugate_#idx("conjugate") (over
  $K$) if $gamma' = phi.alt(gamma)$ for some $K$-automorphism $phi.alt$ of
  $tilde(K)$; this occurs if and only if $gamma$ and $gamma'$ have the same
  minimal polynomial over $K$. It follows from @eq:extended-valuation that
  $abs(gamma) = abs(gamma')$ whenever $gamma$ and $gamma'$ are conjugate.

  Now let
  $
    f(X) = (X - xi_1) dots.c (X - xi_n), quad xi_i in tilde(K), quad xi_1 = xi,
  $
  and set
  $
    h = min {abs(xi_i - xi) : 2 <= i <= n}.
  $
  Since $f(X)$ is separable by hypothesis, the elements
  $xi_1, dots, xi_n in tilde(K)$ are distinct, and so $h > 0$. We shall prove
  that
  $
    beta in tilde(K), abs(beta - xi) < h quad ==> quad xi in K(beta).
  $ <eq:krasner>

  Suppose that @eq:krasner is false, and let $beta$ be a counterexample, so
  $xi in.not K(beta)$. Let $m(X) = minpol_(K(beta)) xi$. Then
  $m(X) divides f(X)$, and $m(X)$ has degree greater than 1. Since $f(X)$ has
  $n$ distinct zeros, namely $xi_1, dots, xi_n$, it follows that $m(xi_i) = 0$
  for some $xi_i != xi$. Therefore the elements $beta - xi$ and $beta - xi_i$
  are conjugate over $K(beta)$, hence over $K$, and so
  $abs(beta - xi) = abs(beta - xi_i)$. But then
  $
    abs(xi - xi_i) <= min (abs(beta - xi), abs(beta - xi_i)) = abs(beta - xi)
    < h,
  $
  which contradicts the choice of $h$. We have thus proved @eq:krasner, which
  may be rephrased as follows:

  _If $beta in tilde(K)$ is closer to $xi$ than any conjugate of $xi$, then
  $xi in K(beta)$._

  _Step 3._ We are now assuming that $n > 1$; it follows that $xi != 0$, since
  otherwise $f(X)$ is reducible. Hence we may choose $d in bold(R)$ such that
  $
    0 < d < abs(xi), quad d dot abs(xi)^(n-1) < h^n,
  $
  keeping the notation of Step~2. We shall show that if the coefficients of
  $g(X)$ are such that
  $
    abs(b_j) <= d^j, quad 1 <= j <= n,
  $
  then $f(X) + g(X)$ is irreducible, and has a zero in $L$.

  We show first that
  $
    abs(a_j) <= abs(xi)^j, quad 1 <= j <= n.
  $ <eq:coefficient-bound>
  #source(295)Indeed, for each such $j$, the coefficient $a_j$ in $f(X)$ is
  (apart from sign) the elementary symmetric function of degree $j$ in the
  quantities ${xi_1, dots, xi_n}$. Since these elements are mutually conjugate
  over $K$, we have $abs(xi_1) = dots = abs(xi_n)$. But then
  @eq:coefficient-bound follows at once, by using the properties
  @def:valuation[(i)–(iv)] of the valuation $|thin|$. (It should be pointed out
  that @eq:coefficient-bound is merely a restatement of
  @lem:irreducible-coefficients-slope[Lemma].)

  Next, for $1 <= j <= n$ we obtain
  $
    abs(b_j) <= d^j < abs(xi)^j,
  $
  whence
  $
    abs(a_j + b_j) <= max (abs(a_j), abs(b_j)) <= abs(xi)^j.
  $
  If $beta in tilde(K)$ is any zero of $f(X) + g(X)$, then
  $f(beta) + g(beta) = 0$, and so we conclude that
  $
    abs(beta)^n = abs(sum_(j=1)^n (a_j + b_j) beta^(n-j))
    <= max_(1 <= j <= n) {abs(xi)^j dot abs(beta)^(n-j)}.
  $ <eq:zero-bound>
  If $abs(xi) < abs(beta)$, then
  $
    max_(1 <= j <= n) {abs(xi)^j dot abs(beta)^(n-j)}
    < max_(1 <= j <= n) {abs(beta)^n} = abs(beta)^n,
  $
  which contradicts @eq:zero-bound. Therefore $abs(beta) <= abs(xi)$.
  Furthermore,
  $
    product_(i=1)^n (beta - xi_i) = f(beta) = -g(beta)
    = -(b_1 beta^(n-1) + dots.c + b_n).
  $
  This gives
  $
    {min_(1 <= i <= n) abs(beta - xi_i)}^n
    <= max_(1 <= j <= n) {abs(b_j) abs(beta)^(n-j)}
    <= max_(1 <= j <= n) {d^j dot abs(xi)^(n-j)} = d dot abs(xi)^(n-1),
  $
  where the last step follows from the fact that $d < abs(xi)$. Since
  $d dot abs(xi)^(n-1) < h^n$, we conclude that
  $
    abs(beta - xi_i) < h quad "for some" i, quad 1 <= i <= n.
  $

  Now let $phi.alt$ be a $K$-automorphism of $tilde(K)$ such that
  $phi.alt(xi_i) = xi$; then
  $
    abs(phi.alt(beta) - xi) = abs(beta - xi_i) < h,
  $
  and $phi.alt(beta)$ is also a zero of $f(X) + g(X)$. Set
  $gamma = phi.alt(beta)$, so $gamma$ is a zero of $f(X) + g(X)$, and
  $abs(gamma - xi) < h$. By Step~2, it follows that $xi in K(gamma)$. Therefore
  $
    (K(gamma) : K) >= (K(xi) : K) = n.
  $
  On the other hand, $gamma$ is a zero of the $n$th degree polynomial
  $f(X) + g(X)$. It #source(296)follows that this polynomial is irreducible in
  $K[X]$, and that $K(gamma) = K(xi)$. Thus $gamma in L$, and $f(X) + g(X)$ is
  separable. This completes the proof.
]

Our second preliminary result is

#lemma[
  Let $R$ be a complete discrete valuation ring, with quotient field $K$ and
  finite residue class field $overline(R)$. Let $W$ be an unramified extension
  of $K$ of degree $n$. Then for each $alpha in u(R)$, there exists an element
  $y in W$ such that
  $
    N_(W slash K) y = alpha, quad W = K(y).
  $
] <lem:unramified-norm-generator>

#proof[
  The result is obvious when $n = 1$, so take $n > 1$ hereafter. Denote
  $N_(W slash K)$ by $N$, for brevity. By @th:unramified-norm-equation we know
  that $alpha = N x$ for some $x in W$, and we must modify $x$ so that it
  generates $W$. By @th:unramified-finite-residue we may set $W = K(omega)$,
  where $omega$ is a primitive $(q^n - 1)$th root of 1 over $K$, and
  $card overline(R) = q$. Then $W slash K$ is a (separable) galois extension;
  its galois group is cyclic of order $n$, and is generated by the Frobenius
  automorphism $sigma$, where $sigma(omega) = omega^q$. Thus there is a
  one-to-one correspondence between the set of divisors of $n$, and the set of
  intermediate fields $L$ between $K$ and $W$. Consequently there are at most
  $n$ such intermediate fields.

  Let us put
  $
    L_j = K(x dot omega^(j(q-1))), quad 0 <= j <= n - 1.
  $
  We have
  $
    N omega^(q-1) = product_(i=0)^(n-1) sigma^i (omega^(q-1))
    = omega^((q-1)(1 + q + dots.c + q^(n-1))) = 1.
  $
  Therefore
  $
    N(x dot omega^(j(q-1))) = N x = alpha, quad 0 <= j <= n - 1.
  $

  If $L_j = W$ for some $j$, then the desired element $y in W$ such that
  $N y = alpha$, $W = K(y)$, can be chosen as $x dot omega^(j(q-1))$, and we are
  through. We shall now assume that each of the $n$ fields $L_0, dots, L_(n-1)$
  is a proper subfield of $W$, and we shall obtain a contradiction. We saw above
  that there are at most $n$ fields between $K$ and $W$, including the extreme
  cases $K$ and $W$. Since each of the $n$ fields ${L_j : 0 <= j <= n - 1}$ is
  assumed to be distinct from $W$, it follows that two of the $L$'s must
  coincide. Suppose that $L_i = L_j$, where $0 <= i < j <= n - 1$. Since
  $alpha in u(R)$ and $N x = alpha$, surely $x != 0$. Thus we may form the
  quotient
  $
    x dot omega^(j(q-1)) slash x dot omega^(i(q-1)) in L_i,
  $
  and so $L_i$ contains an element $omega^(t(q-1))$, where $0 < t <= n - 1$. Now
  $(W : L_i) > 1$ by assumption, and therefore $L_i$ is fixed by some $sigma^s$,
  with $1 <= s < n$, $s divides n$. Thus $s <= n slash 2$. The equation
  $
    sigma^s (omega^(t(q-1))) = omega^(t(q-1))
  $
  #source(297)yields the congruence
  $
    q^s dot t(q - 1) equiv t(q - 1) (mod (q^n - 1)).
  $
  Therefore $q^n - 1$ must divide the positive integer
  $
    lambda = (q^s - 1) t dot (q - 1).
  $
  But
  $
    lambda <= (q^(n slash 2) - 1)(q - 1)(n - 1).
  $
  The reader will easily verify that the right hand expression is always less
  than $q^n - 1$. This gives the desired contradiction, and completes the proof
  of the lemma.
]

#corollary[
  Let $R$ be a complete discrete valuation ring with quotient field $K$, prime
  element $pi$, and finite residue class field $overline(R)$. Then for each
  nonzero $beta in K$, and each positive integer $n$, there exists a monic
  separable irreducible polynomial $f(X) in K[X]$ of degree $n$, with constant
  term $(-1)^n beta$. Furthermore, if $beta in R$ then $f(X)$ may be chosen in
  $R[X]$.
] <cor:polynomial-with-given-constant-term>

#proof[
  Given $beta in K^*$ and $n >= 1$, we need only show that there exist a
  separable extension $L slash K$ of degree $n$, and an element $x in L$ such
  that
  $
    beta = N_(L slash K) x, quad L = K(x).
  $
  Once this is done, we may pick $f(X) = minpol_K x$. Then $f(X)$ is irreducible
  and has degree $n$, since $(L : K) = n$. Further, $f(X)$ is a separable
  polynomial because $L slash K$ is separable. We note also that if $beta in R$,
  then $f(X) in R[X]$ by virtue of @th:irreducible-coefficients. The rest of the
  proof is devoted to showing how to find $L$ and $x$.

  Set $beta = pi^r alpha$, $r in bold(Z)$, $alpha in u(R)$; then
  $v_K (beta) = r$, where $v_K$ is the exponential valuation associated with $R$
  (see §~@ss:extensions-of-complete-fields). If $n divides r$, then put
  $s = r slash n in bold(Z)$, and choose $W$ and $y$ as in
  @lem:unramified-norm-generator. Then
  $
    N_(W slash K) (pi^s y) = pi^(n s) alpha = beta, quad
    W = K(pi^s y), (W : K) = n.
  $
  Hence we may choose $L = W$, $x = pi^s y$, in this case where $n divides r$.

  We now turn to the case where $n divides.not r$, and put
  $
    d = (n, r), quad n = m d, quad r = s d, quad "where" quad (m, s) = 1.
  $
  Since $n divides.not r$, it follows that $m != 1$, and thus that $m > 1$. Now
  let $E slash K$ be an unramified extension of degree $d$. Since $d divides r$,
  we may deduce from the preceding paragraph that there exists an element
  $y in E$ such that
  $
    N_(E slash K) y = beta, quad E = K(y).
  $
  Now $pi$ is also a prime element for the valuation ring of $E$, since
  $E slash K$ is #source(298)unramified. Therefore by
  @th:extensions-complete-fields we have
  $
    r = v_K (beta) = v_E (beta) = (E : K) v_E (y) = d dot v_E (y),
  $
  which shows that
  $
    v_E (y) = r slash d = s.
  $

  Let us choose $t = |s| + 1$, and consider the separable polynomial
  $
    g(X) = X^m + pi^t X + (-1)^m y quad in E[X].
  $
  Let $z$ be a zero of $g(X)$ in some algebraic closure of $E$, and set
  $L = E(z)$. Then $L slash E$ is a separable extension, and $(L : E) <= m$. As
  in @th:extensions-complete-fields we set
  $
    e = e(L slash E), quad f = f(L slash E),
  $
  so $e f = (L : E) <= m$, and $v_L (pi) = e$. Since $g(z) = 0$, we have
  $
    v_L (y) >= min {v_L (z^m), v_L (pi^t z)} = min {m h, e t + h},
  $ <eq:zero-valuation-bound>
  where $h = v_L (z)$. If $m h >= e t + h$, then
  $
    (m - 1) h >= e t > 0.
  $
  Since $m > 1$, this would give $h > 0$, and then from @eq:zero-valuation-bound
  we would obtain
  $
    e s = v_L (y) >= e t + h > e t.
  $
  This is impossible, since $t = |s| + 1$, and so it follows that
  $m h < e t + h$. But then (see @def:exponential-valuation,
  @def:valuation[(v)]), the equation $g(z) = 0$ yields a sharper form of
  @eq:zero-valuation-bound, namely,
  $
    e s = v_L (y) = min {m h, e t + h} = m h.
  $
  Therefore $m divides e s$, whence $m divides e$ since $(m, s) = 1$. This
  proves that $m = e$, and therefore $L slash E$ is a separable extension of
  degree $m$, such that $L = E(z)$. Since $y in K(z)$ and $E = K(y)$, it follows
  that
  $
    L = K(z), quad (L : K) = m d = n, quad L slash K "separable".
  $
  Finally,
  $
    beta = N_(E slash K) y = N_(E slash K) (N_(L slash E) z) = N_(L slash K) z
  $
  by Exercise~@exc:transitivity-trace-norm. This completes the proof of the
  corollary.
]

With these preliminaries settled, we are now ready to prove the following
important result:

#theorem(major: true, title: "Hasse–Schilling–Maass")[
  Let $A$ be a central simple $K$-algebra, where $K$ is a global field, and let
  $alpha in K^*$. Then $alpha$ is the reduced norm of an element of $A$ if and
  only if $alpha_P > 0$ at every infinite prime $P$ of $K$ ramified in $A$.
  #idx("Hasse–Schilling–Maass Theorem", target: [@th:hasse-schilling-maass])
] <th:hasse-schilling-maass>

#proof[
  #source(299)_Step 1._ Since $alpha in K^*$, it follows from
  @th:reduced-norm-matrix-ring that $alpha$ is a reduced norm if and only if
  $alpha$ is the reduced norm of an invertible element of $A$. We are trying to
  prove that
  $
    nr_(A slash K) u(A) = U(A),
  $
  where $U(A)$ is defined by @eq:reduced-norm-positivity-set. Now
  $
    alpha in nr A quad ==> quad alpha_P in nr A_P quad "for all" P quad ==>
    quad alpha in U(A),
  $
  by @eq:global-reduced-norm-local and @eq:local-reduced-norm-criterion. Hence
  we need only prove that, conversely, $U(A) subset nr A$. In what follows, let
  $beta in U(A)$.

  Throughout this proof, let $S$ denote the set of all infinite primes $P$ of
  $K$ which are ramified in $A$. Possibly $S$ is the empty set. Choose $S'$ to
  be a non-empty finite set of finite primes of $K$, including each finite $P$
  ramified in $A$. Then
  $
    P in.not S union S' ==> A_P tilde.op K_P.
  $

  _Step 2._ Let $(A : K) = n^2$. By @cor:polynomial-with-given-constant-term,
  for each $P in S'$ we may find a separable polynomial
  $
    f_P (X) = X^n + a_(1,P) X^(n-1) + dots.c + a_(n-1,P) X + (-1)^n beta quad
    in K_P [X]
  $
  such that $f_P (X)$ is irreducible over $K_P$. If the set $S$ is empty,
  proceed directly to the next paragraph. If $S$ is non-empty, then some
  infinite prime of $K$ ramifies in $A$, so $n$ is even by
  Exercise~@exc:odd-index-unramified-infinite. We then set
  $
    f_P (X) = X^n + (-1)^n beta quad in K_P [X], quad P in S.
  $

  Given any $epsilon > 0$, by @th:strong-approximation we can choose a
  polynomial
  $
    f(X) = X^n + c_1 X^(n-1) + dots.c + c_(n-1) X + (-1)^n beta quad in K[X],
  $
  such that
  $
    cases(
      phi_P (c_i - a_(i,P)) < epsilon"," quad 1 <= i <= n - 1"," quad
      P in S'",",
      phi_P (c_i) < epsilon"," quad P in S.,
    )
  $
  By @lem:perturbed-polynomial-irreducible, if we pick a sufficiently small
  $epsilon$, then $f(X)$ will be irreducible in $K_P [X]$ for each $P in S'$.
  Hence $f(X)$ is also irreducible over $K$, since $S'$ is non-empty.
  Furthermore, since $beta in U(A)$, we have $beta_P > 0$ for each $P in S$.
  Hence if $epsilon$ is small enough, we can be sure that for each $P in S$, the
  polynomial $f(X)$ has no zeros in the real field $K_P$.

  _Step 3._ Now choose an element $x$ in an algebraic closure of $K$, such that
  $f(x) = 0$, and set $L = K(x)$. Then
  $
    (L : K) = n, quad minpol_K x = f(X), quad N_(L slash K) x = beta.
  $
  #source(300)We proceed to calculate the local degrees
  $
    n_frak(p) = (L_frak(p) : K_P), quad P in S union S',
  $
  where for each $P in S union S'$, the prime $frak(p)$ ranges over all primes
  of $L$ extending $P$.

  For each prime $P in S$, the polynomial $f(X)$ has no real zeros in $K_P$.
  From the discussion in §~@ss:extensions-of-valuations, it follows that each
  prime $frak(p)$ of $L$ which extends $P$ must be complex. Therefore
  $n_frak(p) = 2$ for each such $frak(p)$. On the other hand, for $P in S'$ the
  polynomial $f(X)$ is irreducible in $K_P [X]$. Again using
  §~@ss:extensions-of-valuations, we may conclude that $n_frak(p) = n$, and
  indeed that there is only one $frak(p)$ extending $P$.

  Now let ${m_P}$ be the set of local indices of the central simple $K$-algebra
  $A$. Then surely $m_P divides n$ for each $P$, and
  $
    m_P = 1, quad P in.not S union S'; quad m_P = 2, quad P in S.
  $
  Hence for _every_ prime $P$ of $K$, and every prime $frak(p)$ of $L$ extending
  $P$, it follows that $m_P divides (L_frak(p) : K_P)$. Therefore $L$ is a
  splitting field for $A$, by @th:splitting-field-local-criterion.

  Finally, we note that
  $
    (A : K) = n^2 = (L : K)^2.
  $
  Since $L$ splits $A$, it follows from @cor:self-centralizing-embedding that we
  may embed $L$ in $A$ as a self-centralizing maximal subfield of $A$. Therefore
  $
    beta = N_(L slash K) x = nr_(A slash K) x,
  $
  by Exercise~@exc:reduced-char-pol-maximal-subfield, and the proof is finished.
]

#remark(numbered: false)[
  In the above proof, we used the Strong Approximation Theorem
  @th:strong-approximation. It would have been enough to apply a weaker version
  of @th:strong-approximation, obtained by deleting from the conclusion of
  @th:strong-approximation the assertion that "$b in R_P$ for all
  $P != P_1, dots, P_n$". This weaker version is called the _Weak Approximation
  Theorem_, and is true for any domain $R$ (not necessarily a Dedekind domain).
  #idx("Weak Approximation Theorem")
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $K$ be a field with valuation $|thin|$, and $V = dsum_(i=1)^n K v_i$ a
  finite dimensional $K$-space. Define a _norm_ on $V$ by setting
  $
    norm(sum_(i=1)^n alpha_i v_i) = max {abs(alpha_1), dots, abs(alpha_n)},
    quad alpha_i in K.
  $
  Prove the following:
  + $V$ is a metric space relative to this norm, with distance between two
    elements $v, v' in V$ given by $norm(v - v')$.
  + This topology on $V$ is independent of the choice of $K$-basis of $V$.
  + If $K$ is complete with respect to $|thin|$, then $V$ is a complete metric
    space.
] <exc:norm-on-vector-space>

#exercise[
  #source(301)Let $A$ be a central simple $K$-algebra, where $K$ is a field with
  a valuation $|thin|$, and define a norm on $A$ as in the preceding exercise.
  Let $nr: A -> K$ be the reduced norm map. Prove that $nr$ is continuous, that
  is, if $x, y in A$ are such that $norm(x - y)$ is small, then also
  $abs(nr(x) - nr(y))$ is small. #hint[@exc:reduced-norm-continuous][Choose a
    field $E supset K$ such that $(E : K)$ is finite, and $E$ splits $A$. Extend
    the valuation $|thin|$ on $K$ to a norm on $E$. Then prove that each of the
    following maps is continuous:
    $
      A -> E times.o_K A, quad E times.o_K A tilde.equiv M_r (E), quad
      det: M_r (E) -> E,
    $
    where $(A : K) = r^2$.] <hint:reduced-norm-continuous>
] <exc:reduced-norm-continuous>

#exercise[
  Let $A$ be a central simple $K$-algebra, $P$ a finite prime of $K$, $R_P$ the
  $P$-adic valuation ring of $K_P$. Given a finite set of finite primes
  ${P, P_2, dots, P_r}$, show that there exists an element $y in A$ such that
  $
    cases(
      nr_(A slash K) y = "prime element of" R_P",",
      nr_(A slash K) y in u(R_Q) "for" Q = P_2"," dots"," P_r .,
    )
  $
  #hint[@exc:reduced-norm-prime-element][Extend the $P$-adic valuation $phi_P$
    on $K_P$ to a norm $norm(thin)_P$ on $A$ and $A_P$. By
    @th:local-reduced-norms, there exists an $x_P in A_P$ with $nr x_P = pi_P$,
    a preassigned prime element of $R_P$. If $y_P in A_P$ is chosen so that
    $norm(y_P - x_P)_P$ is sufficiently small, then
    $
      nr y_P equiv nr x_P (mod pi_P^2 R_P),
    $
    so $nr y_P$ is also a prime element of $R_P$. Now use
    @th:strong-approximation to choose $y in A$ so that
    $
      norm(y - x_P)_P < epsilon, norm(y - 1)_Q < epsilon "for"
      Q = P_2, dots, P_r,
    $
    with $epsilon$ small. If $epsilon$ is sufficiently small, then $nr y$ will
    have the desired properties.] <hint:reduced-norm-prime-element>
] <exc:reduced-norm-prime-element>

#exercise[
  Let $L$ be a cyclic extension of the algebraic number field $K$, and let
  $A = (L slash K, sigma, a)$ be a cyclic algebra. When is $A$ a totally
  definite quaternion algebra? (See @def:totally-definite-quaternion-algebra.)
] <exc:cyclic-totally-definite>
