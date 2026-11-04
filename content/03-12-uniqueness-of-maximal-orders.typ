#import "main-defs.typ": *
#import "statements.typ": *

== Uniqueness of maximal orders <sec:uniqueness-of-maximal-orders>

We are going to show that $D$ contains a _unique_ maximal $R$-order $Delta$. The
argument will depend strongly on the use of Hensel's Lemma @th:hensel. Let $v$
be the exponential $P$-adic valuation defined on $K$ (see
§~@ss:extensions-of-complete-fields, where $v$ was denoted by $v_K$). Then it is
easily seen that for $a, b in K$ we have
$
  cases(
    "(i)" & v(a) = infinity "if and only if" a = 0,
    "(ii)" & v(a b) = v(a) + v(b) = v(b a),
    "(iii)" & v(a + b) >= min (v(a), v(b)),
    "(iv)" & "The value group of" v "is infinite cyclic,",
  )
$ <eq:valuation-axioms>
where the _value group_#idx("value group (of valuation)") of $v$ is defined to
be ${v(a) : a != 0}$.

#theorem[
  Let $f(X) = alpha_0 X^n + alpha_1 X^(n-1) + dots.c + alpha_n in K[X]$ be
  irreducible. Then
  $
    v(alpha_i) >= min (v(alpha_0), v(alpha_n)), quad 0 <= i <= n.
  $
] <th:irreducible-coefficients>

#proof[
  Let $t = min {v(alpha_i) : 0 <= i <= n}$. If the theorem is false, then
  $t < min (v(alpha_0), v(alpha_n))$. Let $r$ be the largest subscript for which
  $v(alpha_r) = t$. Then $r != 0$, $r != n$, and
  $
    alpha_r^(-1) dot f(X) = beta_0 X^n + dots.c + beta_r X^(n-r) + dots.c
    + beta_n, quad beta_i in R,
  $
  where $beta_r = 1$ and $beta_(r+1), dots, beta_n in P$. However, in
  $overline(R)[X]$ the right hand expression is a product
  $X^(n-r) (1 + overline(beta)_(r-1) X + dots.c + overline(beta)_0 X^r)$ of two
  relatively prime #source(145)polynomials, with the first factor monic. It
  follows by Hensel's Lemma that $alpha_r^(-1) dot f(X)$ is reducible, whence so
  is $f(X)$, a contradiction. This completes the proof.
]

Now let $N_(D slash K)$ and $T_(D slash K)$ be the norm and trace maps, defined
by
$
  charpol_(D slash K) a = X^m - (T_(D slash K) a) X^(m-1) + dots.c
  + (-1)^m N_(D slash K) a, quad a in D,
$
where for the rest of this section we put $(D : K) = m$. We now set
$
  w(a) = m^(-1) dot v(N_(D slash K) a), quad a in D.
$ <eq:skewfield-valuation>

#theorem[
  For $a in D$, let $f(X) = minpol_K a$. Then
  $
    w(a) = (K(a) : K)^(-1) dot v(f(0))
    = (K(a) : K)^(-1) dot v(N_(K(a) slash K) a).
  $
] <th:skewfield-valuation-min-pol>

#proof[
  Since $D$ is a skewfield, $f(X)$ is irreducible, and therefore
  $charpol_(D slash K) a = f(X)^(m slash n)$, where
  $n = "degree of" f(X) = (K(a) : K)$. Therefore
  $
    N_(D slash K) a = (-1)^m dot {f(0)}^(m slash n),
  $
  whence
  $
    w(a) = m^(-1) dot v({f(0)}^(m slash n)) = n^(-1) dot v(f(0)),
  $
  which completes the proof.
]

Using @th:irreducible-coefficients and @th:skewfield-valuation-min-pol, we may
prove the fundamental

#theorem[
  An element $a in D$ is integral over $R$ if and only if
  $N_(D slash K) a in R$, or equivalently, if and only if $w(a) >= 0$.
] <th:integral-iff-norm-integral>

#proof[
  It is obvious that $w(a) >= 0$ if and only if $N a in R$, where we write $N$
  for $N_(D slash K)$. If $a$ is integral over $R$, then
  $charpol_(D slash K) a in R[X]$ by Exercise~@exc:char-pol-integral, whence
  $N a in R$. Conversely, let $N a in R$, and set
  $
    f(X) = X^n + alpha_1 X^(n-1) + dots.c + alpha_n = minpol_K a.
  $
  Then $f(0) = alpha_n$, and since $plus.minus N a$ is a power of $f(0)$, it
  follows that $alpha_n in R$. But $f(X)$ is irreducible in $K[X]$, so by
  @th:irreducible-coefficients we deduce that
  $
    v(alpha_i) >= min (v(1), v(alpha_n)) = 0, quad 0 <= i <= n.
  $
  Hence $f(X) in R[X]$, so $a$ is integral over $R$. This completes the proof.
]

#theorem[
  The map $w$ is a discrete valuation on $D$ which extends $v$, that is, $w$
  satisfies conditions @eq:valuation-axioms, and $w(alpha) = v(alpha)$,
  $alpha in K$.
] <th:skewfield-valuation>

#proof[
  Consider the conditions @eq:valuation-axioms on $w$; (i) clearly holds, since
  $a = 0$ if and only if $N a = 0$. Condition (ii) is satisfied since $N$ is
  multiplicative, and #source(146)$v$ satisfies (ii). For $alpha in K$, we have
  $w(alpha) = v(alpha)$ by @th:skewfield-valuation-min-pol. Next, the value
  group of $w$, ${w(a) : a in D, a != 0}$, is a nonzero additive subgroup of
  $m^(-1) bold(Z)$, and is therefore isomorphic to $bold(Z)$.

  It remains for us to show that $w$ satisfies (iii), and for this it suffices
  to consider the case where $a = 1$ and $w(b) >= 0$, with $b in D$. But then
  $b$ is integral over $R$ by @th:integral-iff-norm-integral, so by
  @cor:sum-product-integral also $1 + b$ is integral over $R$. Hence
  $
    w(1 + b) >= 0 = min (w(1), w(b)),
  $
  as desired. This completes the proof.
]

Let us set
$
  Delta = {a in D : w(a) >= 0} = {a in D : N_(D slash K) a in R}.
$ <eq:skewfield-valuation-ring>
Then $Delta$ is a ring containing $R$, by @th:skewfield-valuation. We call
$Delta$ the _valuation ring_#idx("valuation ring") of $w$. We shall show in
@th:skewfield-ef that $Delta$ is finitely generated as $R$-module. Taking this
for granted, we have

#theorem(major: true)[
  $Delta$ is the unique maximal $R$-order in $D$, and is the integral closure of
  $R$ in $D$.
] <th:skewfield-unique-maximal-order>

#proof[
  Clearly $K dot Delta = D$, and so $Delta$ is an $R$-order in $D$. But by
  @th:order-elements-integral, every element of an $R$-order in $D$ is integral
  over $R$, hence lies in $Delta$ by @th:integral-iff-norm-integral. Therefore
  $Delta$ is the unique maximal $R$-order in $D$, and the result is proved.
]

We are now going to prove that $w$ is the _unique_ extension of $v$ to $D$
satisfying @eq:valuation-axioms, and begin with

#lemma(note: [For a generalization of this lemma, see the discussion of Newton's
  polygon in Weiss [@bib:Weiss1963, section~3.1].])[
  Let $f(X) = X^n + alpha_1 X^(n-1) + dots.c + alpha_n in K[X]$ be irreducible.
  Then
  $
    v(alpha_k) >= k / n dot v(alpha_n), quad 1 <= k <= n.
  $
] <lem:irreducible-coefficients-slope>

#proof[
  Let $E$ be a splitting field for $f(X)$ over $K$, and write
  $f(X) = (X - beta_1) dots.c (X - beta_n)$, $beta_i in E$. Let $v'$ be the
  extension of $v$ to $E$ defined as in @eq:skewfield-valuation, namely,
  $
    v'(beta) = (E : K)^(-1) dot v(N_(E slash K) beta), quad beta in E.
  $
  But $minpol_K beta_j = f(X)$, so by @th:skewfield-valuation-min-pol we have
  $
    v'(beta_j) = (K(beta_j) : K)^(-1) dot v(f(0)) = n^(-1) dot v(alpha_n)
  $
  for each $j$. However, $plus.minus alpha_k$ is the $k$th elementary symmetric
  polynomial in #source(147)$beta_1, dots, beta_n$, so by @eq:valuation-axioms
  (ii) and (iii) we obtain
  $
    v(alpha_k) = v'(alpha_k) >= k / n dot v(alpha_n)
  $
  for each $k$, as desired.
]

#theorem[
  The valuation $w$ is the unique extension of $v$ to $D$ having properties
  @eq:valuation-axioms.
] <th:skewfield-valuation-unique>

#proof[
  Let $u : D -> bold(R) union {infinity}$ be another such extension of $v$. If
  $u != w$, there exists a nonzero $a in D$ such that $u(a) != w(a)$. Replacing
  $a$ by $a^(-1)$ if need be, we may assume that $u(a) > w(a)$. Let
  $
    f(X) = minpol_K a = X^n + alpha_1 X^(n-1) + dots.c + alpha_n in K[X].
  $
  Then $w(a) = v(alpha_n) slash n$ by @th:skewfield-valuation-min-pol, while
  $v(alpha_j) >= (j slash n) v(alpha_n)$ by @lem:irreducible-coefficients-slope,
  since $f(X)$ is irreducible. Therefore
  $
    u(alpha_j dot a^(n-j)) = v(alpha_j) + (n - j) u(a)
    > j / n dot v(alpha_n) + (n - j) / n dot v(alpha_n) = v(alpha_n),
  $
  for $0 <= j <= n - 1$, where $alpha_0 = 1$. But now
  $
    alpha_n = -alpha_(n-1) dot a - alpha_(n-2) dot a^2 - dots.c - a^n,
  $
  whence
  $
    v(alpha_n) = u(alpha_n) >= min {u(alpha_j dot a^(n-j)) : 0 <= j <= n - 1}
    > v(alpha_n).
  $
  This gives a contradiction, so the theorem is proved.
]

The preceding discussion is of course valid for the special case where $D$ is an
extension field of the complete $P$-adic field $K$. It shows that the $P$-adic
valuation on $K$ can be extended to a discrete valuation on $D$, by means of
formula @eq:skewfield-valuation, and that this extension is unique (up to
equivalence).
