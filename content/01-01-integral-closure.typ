#import "main-defs.typ": *
#import "statements.typ": *

== Integral closure <sec:integral-closure>

Throughout this section let $K$ be a field, and $A$ a finite dimensional
$K$-algebra. Denote its dimension by $(A : K)$ or $dim_K A$.

=== Minimum and characteristic polynomial; norm, trace <ss:min-char-pol>

Let $K[X]$ denote the domain of polynomials over $K$ in an indeterminate $X$. An
element $f(X) in K[X]$ is _monic_ if its leading coefficient equals 1. Let $V$
be a finite dimensional $K$-space, and $phi$ a $K$-linear transformation on $V$.
We may view $V$ as a left $K[X]$-module, by letting $X$ act as $phi$ on $V$.
Since $(V : K)$ is finite, it is clear that $V$ is a finitely generated module
over the principal ideal domain $K[X]$. By the Structure Theorem for such
modules (see Curtis–Reiner [@bib:Curtis1962, §~16]), there is a
$K[X]$-isomorphism
#idx("monic")
$
  V tilde.equiv dsum_(i=1)^t K[X] slash (h_i (X)), quad h_i (X) in K[X].
$ <eq:structure-theorem-kx>
Each $h_i (X)$ is nonzero in $K[X]$ since $(V : K)$ is finite. As is well known,
the #source(11)characteristic polynomial#idx("characteristic polynomial") of
$phi$ acting on $V$ is given by
$
  charpol_K phi = product_(i=1)^t h_i (X).
$ <eq:char-pol-product>
On the other hand, let $f(X) in K[X]$; then $f(phi)$ acts on $V$ just as $f(X)$
acts on the right hand expression in @eq:structure-theorem-kx. Hence
$f(phi) = 0$ if and only if $f(X)$ annihilates this right hand expression. There
is thus a unique monic polynomial $f(X) in K[X]$, of least degree, such that
$f(phi) = 0$; call this polynomial the _minimum polynomial_ of $phi$. It is
given by
#idx("minimum polynomial")
$
  minpol_K phi = lcm {h_i (X) : 1 <= i <= t}.
$ <eq:min-pol-lcm>
From @eq:char-pol-product and @eq:min-pol-lcm we have at once

#theorem[
  Let $phi$ be a $K$-linear transformation on the finite dimensional $K$-space
  $V$, and let
  $
    f(X) = minpol_K phi, quad g(X) = charpol_K phi.
  $
  Then $f(X)$ divides $g(X)$ in $K[X]$; furthermore, $f(X)$ and $g(X)$ have the
  same irreducible factors in $K[X]$, apart from multiplicities. Finally, if
  $h(X) in K[X]$, then $h(phi) = 0$ if and only if $f(X)$ divides $h(X)$.
] <th:min-pol-divides-char-pol>

Now let $A$ be a finite dimensional $K$-algebra. Each $alpha in A$ determines a
$K$-linear transformation $alpha_L$ on $A$, where $alpha_L$ is the left
multiplication $x -> alpha x$, $x in A$. Clearly
$
  (r alpha + s beta)_L = r alpha_L + s beta_L, quad
  (alpha beta)_L = alpha_L dot beta_L,
$ <eq:left-multiplication>
for all $r, s in K$, $alpha, beta in A$. Further, $alpha_L = 0$ if and only if
$alpha = 0$, since $A$ has a unity element. Therefore the map
$alpha -> alpha_L$, $alpha in A$, is a $K$-algebra isomorphism of $A$ into the
ring $Hom_K (A, A)$ of $K$-linear transformations on $A$. Now define
$
  minpol_K alpha = minpol_K alpha_L, quad
  charpol_(A slash K) alpha = charpol_K alpha_L.
$ <eq:min-char-pol-of-element>
For $h(X) in K[X]$ we have $h(alpha_L) = h(alpha)_L$, and thus $h(alpha) = 0$ if
and only if $h(alpha_L) = 0$. This shows that $minpol_K alpha$ is the unique
monic polynomial $f(X) in K[X]$, of least degree, such that $f(alpha) = 0$. For
later use, we record explicitly the following consequence of
@th:min-pol-divides-char-pol:

#theorem[
  Let $A$ be a finite dimensional $K$-algebra. For $alpha in A$, let
  $
    f(X) = minpol_K alpha, quad g(X) = charpol_(A slash K) alpha.
  $
  Then $f(X)$ is the unique monic polynomial in $K[X]$, of least degree, such
  that $f(alpha) = 0$; it has the property that $f(X) | h(X)$ for each
  $h(X) in K[X]$ such that #source(12)$h(alpha) = 0$. Further, $f(X) | g(X)$,
  and the polynomials $f(X)$, $g(X)$ have the same irreducible factors in
  $K[X]$, apart from multiplicities.
] <th:min-pol-of-element>

A remark about notation seems called for. If $B$ is a $K$-algebra containing
$A$, then each $alpha in A$ also lies in $B$. Viewing $alpha$ as element of $B$
does not affect the calculation of $minpol_K alpha$, and so we have suppressed
the subscript $A$ in this notation. On the other hand,
$charpol_(A slash K) alpha$ certainly depends on the choice of $A$, since it
must be computed by letting $alpha$ act on a $K$-basis for $A$; indeed,
$charpol_(A slash K) alpha != charpol_(B slash K) alpha$ if $B != A$, since
$charpol_(A slash K) alpha$ has degree $(A : K)$.

Suppose now that $A = dsum_(i=1)^m K u_i$, and let $alpha in A$. We may write
$
  alpha dot u_j = sum_(i=1)^m a_(i j) u_i, quad a_(i j) in K, quad
  1 <= j <= m.
$
Then
$
  charpol_(A slash K) alpha & = det(delta_(i j) X - a_(i j)) \
                            & = X^m - (T_(A slash K) alpha) X^(m-1) + dots.c
                              + (-1)^m N_(A slash K) alpha.
$ <eq:char-pol-trace-norm>
We call $T_(A slash K)$ the _trace_ map, and $N_(A slash K)$ the _norm_ map.
Clearly #idx("trace")#idx("norm (of element)")
$
  T_(A slash K) alpha = "trace of" alpha_L, quad
  N_(A slash K) alpha = det alpha_L,
$
so from @eq:left-multiplication we deduce
$
  cases(
    T(r alpha + s beta) = r T(alpha) + s T(beta),
    N(alpha beta) = N(alpha) dot N(beta)"," quad N(r alpha) = r^m N(alpha)",",
  )
$ <eq:trace-norm-properties>
for $r, s in K$, $alpha, beta in A$. Here, $m = (A : K)$.

=== Integral elements <ss:integral-elements>

Now let $R$ be an integral domain with quotient field $K$, and let $A$ be a
finite dimensional $K$-algebra. An element $alpha in A$ is _integral_ over $R$
if $f(alpha) = 0$ for some monic polynomial $f(X) in R[X]$.
#idx("integral element")

#theorem[
  For an element $alpha in A$, the following three conditions are equivalent:
  + $alpha$ is integral over $R$.
  + $R[alpha]$ is a finitely generated $R$-module.
  + $alpha$ is contained in some subring $B$ of $A$, such that $B$ is a finitely
    generated $R$-module.
] <th:integral-criteria>

#proof[
  #source(13)If (i) holds, then there is a relation
  $
    alpha^n = a_1 alpha^(n-1) + dots.c + a_n, quad a_i in R.
  $
  It is then obvious that
  $
    R[alpha] = R + R alpha + dots.c + R alpha^(n-1),
  $
  a finitely generated $R$-module. Thus (i) implies (ii). Clearly (ii) implies
  (iii), by choosing $B = R[alpha]$.

  To prove that (iii) implies (i), let us write
  $
    B = sum_(i=1)^n R beta_i, quad beta_i in B.
  $
  Since $B$ is a ring, and $alpha in B$, it follows that each
  $alpha beta_i in B$. Therefore we have
  $
    alpha beta_i = sum_(j=1)^n a_(i j) beta_j, quad a_(i j) in R, quad
    1 <= i <= n.
  $
  We may rewrite these equations as
  $
    sum_(j=1)^n (alpha delta_(i j) - a_(i j)) beta_j = 0, quad 1 <= i <= n.
  $
  Let $d = det(alpha delta_(i j) - a_(i j)) in B$. By Cramer's Formula, it
  follows that $d dot beta_j = 0$ for $1 <= j <= n$. Therefore $d dot B = 0$,
  and hence $d = 0$, since $B$ is a ring with unity element. This shows that
  $alpha$ is a zero of the monic polynomial
  $det(X delta_(i j) - a_(i j)) in R[X]$, and thus $alpha$ is integral over $R$.
  We have now shown that (iii) implies (i), and the theorem is proved.
]

#corollary[
  Let $alpha, beta in A$ be such that $alpha beta = beta alpha$. If both $alpha$
  and $beta$ are integral over $R$, then so are $alpha plus.minus beta$ and
  $alpha beta$.
] <cor:sum-product-integral>

#proof[
  Since $alpha$ and $beta$ are integral over $R$, by @th:integral-criteria we
  may write
  $
    R[alpha] = sum_(i=1)^k R u_i, quad R[beta] = sum_(j=1)^m R v_j.
  $
  Since $alpha beta = beta alpha$, every element of $R[alpha]$ commutes with
  every element of $R[beta]$, and therefore
  $
    R[alpha, beta] = sum_(i, j) R u_i v_j.
  $
  Thus $R[alpha, beta]$ is a finitely generated $R$-module, and is a subring of
  $A$. It follows from @th:integral-criteria that _every_ element of
  $R[alpha, beta]$ is integral over $R$, and hence the corollary is established.
]

#remark(kind: "Remarks", numbered: false)[
  (i) A slightly simpler proof can be given when $R$ is a noetherian #source(
    14,
  )domain (see section~@ss:modules). Keep the above notation, and let
  $x in R[alpha, beta]$. Then $R[x]$ is an $R$-submodule of the finitely
  generated $R$-module $R[alpha, beta]$. Hence $R[x]$ is also finitely generated
  as $R$-module, and thus $x$ is integral over $R$ by @th:integral-criteria.

  (ii) If $alpha$ and $beta$ are integral elements which do not commute, it may
  well occur that $alpha + beta$ is _not_ integral. For example, let
  $R = bold(Z)$, $K = bold(Q)$, $A = M_2 (bold(Q))$ (the algebra of all
  $2 times 2$ matrices with entries in $bold(Q)$). Let
  $
    alpha = mat(0, 1/2; 0, 0), quad beta = mat(0, 0; 1/2, 0).
  $
  Both $alpha$ and $beta$ satisfy the equation $X^2 = 0$, and so are integral
  over $bold(Z)$. However,
  $
    minpol_bold(Q) (alpha + beta) = X^2 - 1/4 in.not bold(Z)[X].
  $
  Therefore $alpha + beta$ is not integral over $bold(Z)$, by
  @th:integral-over-integrally-closed below.
]

=== Integral closure <ss:integral-closure>

The _integral closure_ of $R$ in $A$ is the set of all elements of $A$ which are
integral over $R$. If $A$ is a _commutative_ $K$-algebra, then by
@cor:sum-product-integral the integral closure of $R$ in $A$ is a subring of
$A$. If $A$ is not commutative, the integral closure need not be a ring.
#idx("integral closure")

#definition(formal: true)[
  The integral domain $R$ is _integrally closed_ if the integral closure of $R$
  in its quotient field $K$ coincides with $R$. Thus, $R$ is integrally closed
  if for $alpha in K$,
  $
    f(alpha) = 0, f(X) in R[X], f(X) "monic" => alpha in R.
  $
  #idx("integrally closed", target: [@def:integrally-closed])
] <def:integrally-closed>

#lemma(kind: [Gauss' Lemma])[
  Let $R$ be an integrally closed domain with quotient field $K$. Let
  $f(X) in R[X]$ be a monic polynomial, and suppose that
  $
    f(X) = g(X) dot h(X),
  $
  where $g(X)$ and $h(X)$ are monic polynomials in $K[X]$. Then both $g(X)$ and
  $h(X)$ lie in $R[X]$.
  #idx("Gauss' Lemma", target: [@lem:gauss])
] <lem:gauss>

#proof[
  Let $K'$ be a finite extension of $K$ which is a splitting field for $f(X)$,
  and write
  $
    f(X) = product (X - x_i), quad x_i in K'.
  $
  Let $R'$ denote the integral closure of $R$ in $K'$. Since $f(X) in R[X]$ is
  monic, and $f(x_i) = 0$ for each $i$, it follows that each $x_i in R'$.

  In $K'[X]$ we have
  $
    g(X) dot h(X) = product (X - x_i),
  $
  #source(15)whence both $g(X)$ and $h(X)$ are expressible as partial products
  $product' (X - x_i)$. But $R'$ is a ring by @cor:sum-product-integral, so both
  $g(X)$ and $h(X)$ have coefficients in $R'$. The coefficients of $g(X)$ and
  $h(X)$ are thus in $R' inter K$. However, $R' inter K = R$, because $R$ is
  integrally closed. Thus both $g(X)$ and $h(X)$ lie in $R[X]$, and the lemma is
  proved.
]

In order to determine whether an element $alpha in A$ is integral over $R$, we
must in theory consider _all_ monic polynomials $f(X) in K[X]$ such that
$f(alpha) = 0$, and then we must see whether any such $f(X)$ lies in $R[X]$. In
practice, however, this task is considerably simplified by use of the following
result.

#theorem[
  Let $R$ be an integrally closed domain with quotient field $K$, and let $A$ be
  a finite dimensional $K$-algebra. An element $alpha in A$ is integral over $R$
  if and only if
  $
    minpol_K alpha in R[X].
  $
] <th:integral-over-integrally-closed>

#proof[
  If $minpol_K alpha in R[X]$, it is clear that $alpha$ is integral over $R$.
  Conversely, let $g(X) = minpol_K alpha$, and assume that $alpha$ is integral
  over $R$. Then $f(alpha) = 0$ for some monic polynomial $f(X) in R[X]$.
  Therefore $f(X) = g(X) dot h(X)$ for some monic polynomial $h(X) in K[X]$. It
  then follows from Gauss' Lemma that $g(X) in R[X]$, as desired.
]

We shall conclude this section by listing some examples of integrally closed
domains. Proofs are available in standard references such as Bourbaki
[@bib:Bourbaki1964, Ch.~5, §~1] and Zariski–Samuel [@bib:Zariski1958, Ch.~V,
§~3].

#example(kind: "Examples of integrally closed domains", plain: true)[
  #enum(
    numbering: "(a)",
    [Every principal ideal domain is integrally closed.],
    [Every unique factorization domain is integrally closed.],
    [Every Dedekind domain is integrally closed (see
      §~@ss:ideal-theory-modules).],
    [Let $R$ be a domain with quotient field $K$, and let $K'$ be any extension
      field of $K$. Then the integral closure of $R$ in $K'$ is always
      integrally closed.],
    [Let $S$ be any multiplicative subset of $R$ (see §~@ss:rings-of-quotients).
      If $R$ is integrally closed, so is the ring of quotients $S^(-1) R$.],
    [Let $K[x_1, dots, x_n]$ be the polynomial domain in $n$ indeterminates over
      a field $K$ (or more generally, over a unique factorization domain $K$).
      Then $K[x_1, dots, x_n]$ is also a unique factorization domain, and thus
      is integrally closed by (b).#idx("integrally closed")],
  )
] <exm:integrally-closed-domains>

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#source(16)
#exercise[
  Keep the notation and hypotheses of @th:integral-over-integrally-closed. Show
  that an element $alpha in A$ is integral over $R$ if and only if
  $charpol_(A slash K) alpha in R[X]$. #hint[@exc:char-pol-integral][Use
    @th:min-pol-of-element and
    @th:integral-over-integrally-closed.] <hint:char-pol-integral>
] <exc:char-pol-integral>

#exercise[
  Let $A$ be a finite dimensional $K$-algebra, and let $L$ be any extension
  field of $K$. Each element $a in A$ gives rise to an element $1 times.o a$ of
  the $L$-algebra $L times.o_K A$. Prove that
  $
    charpol_(L times.o_K A slash L) 1 times.o a = charpol_(A slash K) a.
  $
  In other words, $charpol_(A slash K) a$ is not affected by the change of
  ground field from $K$ to $L$.
] <exc:char-pol-ground-field>

#exercise[
  Let $E supset K$ be fields, and let $(E : K) = n$. Each $alpha in E$
  corresponds to a matrix $tilde(alpha) in M_n (K)$, obtained by letting $alpha$
  act as left multiplication on a $K$-basis of $E$. Show by induction on $r$
  that for each matrix $(alpha_(i j)) in M_r (E)$
  $
    det(tilde(alpha)_(i j)) = N_(E slash K) {det(alpha_(i j))}.
  $
] <exc:determinant-norm>

#exercise[
  Let $L$ be a finite galois extension field of $K$, with galois group $G$. Show
  that for $a in L$,
  $
    charpol_(L slash K) a = product_(sigma in G) (X - a^sigma),
  $
  and hence
  $
    T_(L slash K) a = sum_(sigma in G) a^sigma, quad
    N_(L slash K) a = product_(sigma in G) a^sigma.
  $
  #hint[@exc:galois-char-pol][Let
    $
      f(X) = minpol_K a = product_(i=1)^n (X - a_i), quad a_i in L.
    $
    Then $product_(sigma in G) (X - a^sigma) in K[X]$, hence is a power of
    $f(X)$. Then compare degrees of $charpol_(L slash K) a$ and
    $product_(sigma in G) (X - a^sigma)$.] <hint:galois-char-pol>
] <exc:galois-char-pol>

#exercise[
  Keep the notation of Exercise~@exc:determinant-norm, and let $A$ be a finite
  dimensional $E$-algebra. Prove that for $a in A$,
  $
    T_(A slash K) a = T_(E slash K) (T_(A slash E) a), quad
    N_(A slash K) a = N_(E slash K) (N_(A slash E) a).
  $
  #hint[@exc:transitivity-trace-norm][Let
    $
      A = dsum E x_i, quad a x_j = sum alpha_(i j) x_i, quad alpha_(i j) in E.
    $
    Relative to a suitable $K$-basis of $A$, the $K$-linear transformation $a_L$
    on $A$ corresponds to the matrix $(tilde(alpha)_(i j))$. Hence
    $
      T_(A slash K) a & = "trace of" (tilde(alpha)_(i j))
                        = sum_i "trace of" tilde(alpha)_(i i) \
                      & = sum_i T_(E slash K) alpha_(i i)
                        = T_(E slash K) (T_(A slash E) a).
    $
    A similar result holds for norms, by
    Exercise~@exc:determinant-norm.] <hint:transitivity-trace-norm>
] <exc:transitivity-trace-norm>
