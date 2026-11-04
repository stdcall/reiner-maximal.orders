#import "main-defs.typ": *
#import "statements.typ": *

== Maximal orders (complete local case) <sec:maximal-orders-complete-local-case>

In this section we assume always that $R$ is a complete discrete valuation ring.
We know by §~@sec:uniqueness-of-maximal-orders that the skewfield $D$ contains a
unique maximal $R$-order $Delta$, which is the integral closure of $R$ in $D$.
Denote by $pi_D$ a prime element of $Delta$, and let $frak(p) = pi_D Delta$. We
have seen in @th:skewfield-order-ideals that the powers ${frak(p)^m}$ give all
nonzero one-sided ideals of $Delta$, and that these ideals are necessarily
two-sided ideals. We set $overline(Delta) = Delta slash frak(p)$, a skewfield of
finite dimension over the field $overline(R)$.

Let $A = M_r (D)$ be a central simple $K$-algebra. Our aim here is to show that
$M_r (Delta)$, and its conjugates, give all possible maximal $R$-orders in $A$.
We shall also study the one-sided and two-sided ideals of such orders.

#theorem(major: true)[
  + #source(180)Let $Lambda = M_r (Delta)$. Then $Lambda$ is a maximal $R$-order
    in $A$, and has a unique maximal two-sided ideal $pi_D Lambda$. The powers
    $
      (pi_D Lambda)^m = pi_D^m Lambda, quad m = 0, 1, 2, dots,
    $
    give all of the nonzero two-sided ideals of $Lambda$.
  + Every maximal $R$-order in $A$ is of the form $u Lambda u^(-1)$ for some
    $u in u(A)$, and each such ring is a maximal order.
  + Every maximal order $Lambda'$ is left and right hereditary, and each of its
    one-sided ideals is principal. The unique maximal two-sided ideal of
    $u Lambda u^(-1)$ is $u dot pi_D Lambda dot u^(-1)$, that is,
    $u pi_D u^(-1) dot u Lambda u^(-1)$.
] <th:complete-local-maximal-orders>

#proof[
  We know by @th:matrix-maximal-order that $Lambda$ is a maximal order. Keeping
  the notation @eq:order-matrix-form, we set $M = dsum m_i Delta$; then we may
  identify $Lambda$ with $Hom_Delta (M, M)$. Since $M_Delta$ is a progenerator
  for the category $cal(M)_Delta$, it follows from
  @cor:progenerator-morita-equivalence that $Lambda$ is Morita equivalent to
  $Delta$, relative to the Morita context derived from $M_Delta$. By
  @cor:matrix-ring-ideals, the two-sided ideals of $Lambda$ are given by
  $M_r (I)$, with $I$ ranging over the two-sided ideals of $Delta$. But each
  nonzero $I$ is some $pi_D^m Delta$, by @th:skewfield-order-ideals. This proves
  (i), once we observe that
  $
    M_r (pi_D^m Delta) = pi_D^m dot M_r (Delta) = (pi_D Lambda)^m.
  $
  Furthermore, every one-sided ideal of $Delta$ is isomorphic to $Delta$ by
  @th:skewfield-order-ideals, whence $Delta$ is left and right hereditary. By
  Exercise~@exc:equivalence-preserves-hereditary, we may conclude that also
  $Lambda$ is left and right hereditary.

  Now let us prove that every right ideal of $Lambda$ is
  principal,#footnote[Caution: A principal ideal $x Lambda$ is not isomorphic to
    $Lambda$, except when $x in u(A)$.] that is, has the form $x Lambda$ for
  some $x in Lambda$. By @th:morita-equivalence, every right ideal of $Lambda$
  can be written as $Hom_Delta (M, L)$ for some $Delta$-submodule $L$ of $M$.
  However, $M$ is $Delta$-free, and every right ideal of $Delta$ is principal,
  and is isomorphic to $Delta$. Hence by @th:hereditary-submodules-of-free we
  may write $L = dsum_(j=1)^s l_j Delta$, a free $Delta$-module on $s$
  generators, where necessarily $s <= r$. Let $Delta^(s times r)$ denote the set
  of $s times r$ matrices with entries in $Delta$. There is then a bijection
  $Hom_Delta (M, L) <-> Delta^(s times r)$, given by $f <-> U_f$, where
  $
    f(m_1, dots, m_r) = (l_1, dots, l_s) U_f.
  $
  On the other hand, there is a unique $B in Delta^(r times s)$ such that
  $
    (l_1, dots, l_s) = (m_1, dots, m_r) B,
  $
  and thus we have
  $
    f(m_1, dots, m_r) = (m_1, dots, m_r) dot B U_f.
  $
  Comparing this with @eq:order-matrix-form, it follows that $Hom_Delta (M, L)$
  can be identified with the right ideal $B dot Delta^(s times r)$ of
  $M_r (Delta)$. But for each $U in Delta^(s times r)$, we have
  #source(181)
  $
    B dot U = mat(delim: "[", B, 0) mat(delim: "[", U; *),
  $
  where the right-hand expression is a product of two $r times r$ matrices.
  Therefore
  $
    B dot Delta^(s times r) = mat(delim: "[", B, 0) dot M_r (Delta),
  $
  and so we have shown that the given right ideal of $Lambda$ is principal, with
  generator $mat(delim: "[", B, 0)$. A corresponding statement holds for left
  ideals of $Lambda$, by symmetry. (A rather different proof of these facts is
  given in @th:local-hereditary-principal.)

  Turning next to the proof of (ii), let $Lambda'$ be another maximal order in
  $A$. Then $Lambda' Lambda$ is a full right $Lambda$-lattice in $A$, so there
  exists a nonzero $alpha in R$ such that $alpha Lambda' Lambda subset Lambda$.
  Then $alpha Lambda' Lambda$ is a right ideal of $Lambda$, hence is principal
  by the above, and so $Lambda' Lambda = u Lambda$ for some $u in A$. Clearly
  $A = u A$, whence $u in u(A)$ by @th:one-sided-inverse-noetherian. Therefore
  $
    u Lambda = Lambda' Lambda = Lambda' dot Lambda' Lambda
    = Lambda' dot u Lambda supset Lambda' u,
  $
  and thus $Lambda' subset u Lambda u^(-1)$. But $u Lambda u^(-1)$ is also an
  order, and hence $Lambda' = u Lambda u^(-1)$ since $Lambda'$ is maximal.

  Finally, the inner automorphism of $A$ given by $x -> u x u^(-1)$, $x in A$,
  carries $Lambda$ onto $Lambda'$. The assertions about $Lambda'$ follow at once
  from those about $Lambda$, and the proof is complete.
]

#corollary[
  Let $A = Hom_D (V, V)$, where $D$ is a skewfield with center $K$, and where
  $V$ is a simple left $A$-module which is a right vector space over $D$. Let
  $Delta$ be the maximal $R$-order in $D$, and let $Lambda$ be any maximal
  $R$-order in $A$. Then there exists a full free $Delta$-lattice $M$ in $V$
  such that $Lambda = Hom_Delta (M, M)$. Conversely, each such $Lambda$ is
  maximal.
] <cor:complete-local-maximal-endomorphisms>

#proof[
  Let $N$ be any free $Delta$-lattice spanning $V$, and set
  $Lambda' = Hom_Delta (N, N)$. By the above theorem, there exists $u in u(A)$
  such that $Lambda = u Lambda' u^(-1)$. But then choose $M = u N$, and we have
  $
    Hom_Delta (u N, u N) = u dot Hom_Delta (N, N) dot u^(-1) = Lambda,
  $
  as desired. Note that since $N_Delta$ is free, so is $M_Delta$. The fact that
  each $Hom_Delta (M, M)$ is maximal has already been observed in
  @th:complete-local-maximal-orders[(i)].
]

Another important consequence of @th:complete-local-maximal-orders is

#corollary[
  For every maximal $R$-order $Lambda$ in $A$, we have
  $
    rad Lambda = pi_D Lambda, quad
    Lambda slash rad Lambda tilde.equiv M_r (Delta slash rad Delta),
  $
  where "rad" denotes Jacobson radical, and where $Delta slash rad Delta$ is a
  skewfield.
] <cor:complete-local-radical>

#proof[
  #source(182)By @cor:complete-local-maximal-endomorphisms we may choose
  $Lambda = M_r (Delta)$. We may write $rad Lambda = pi_D^m Lambda$ for some
  $m > 0$. If $m > 1$, then $Lambda slash rad Lambda$ contains the nonzero
  nilpotent ideal $pi_D Lambda slash rad Lambda$, which is impossible since
  $Lambda slash rad Lambda$ is semisimple. Thus $m = 1$, and
  $
    Lambda slash rad Lambda tilde.equiv M_r (Delta slash pi_D Delta)
    = M_r (Delta slash rad Delta).
  $
  This finishes the proof.
]

Now let $X$ be any full $R$-lattice in $A$, and define its left and right orders
as in @eq:left-order, @eq:right-order.

#theorem[
  $O_l (X)$ is a maximal order if and only if $O_r (X)$ is a maximal order.
] <th:left-right-orders-maximal>

#proof[
  Let $Lambda = O_r (X)$ be maximal, and set $Lambda' = O_l (X)$. Then $X$ is a
  right $Lambda$-lattice in $A$, so as in @th:complete-local-maximal-orders we
  may write $X = u Lambda$ for some $u in u(A)$. Then
  $
    u Lambda u^(-1) dot X subset X,
  $
  whence $u Lambda u^(-1) subset Lambda'$. Since $u Lambda u^(-1)$ is a maximal
  order, we obtain $u Lambda u^(-1) = Lambda'$, and so $Lambda'$ is maximal, as
  claimed.
]

Keeping the notation of @th:complete-local-maximal-orders, let us determine all
one-sided ideals of $Lambda$, and especially the maximal such ideals. We begin
with an easy result.

#theorem[
  Every matrix with entries in $Delta$ can be diagonalized by means of
  elementary row and column operations. Given any $x in Delta^(s times r)$,
  there exist matrices $u in u(M_s (Delta))$, $v in u(M_r (Delta))$, such that
  $
    u x v = diag(pi_D^(a_1), dots, pi_D^(a_s)), quad
    0 <= a_1 <= dots.c <= a_s.
  $
  The integers $a_1, dots, a_s$ are uniquely determined by $x$. (Possibly some
  of the ${a_i}$ are infinite, and we interpret $pi_D^infinity$ as 0.)
] <th:skewfield-matrix-diagonalization>

#proof[
  One can imitate the usual proof for the case where $Delta$ is a (commutative)
  principal ideal domain. Indeed, the argument is even simpler in this case,
  since $Delta$ is a local ring without zero divisors, and the fact that
  multiplication in $Delta$ is non-commutative does not cause any difficulties.
  We shall not give the details of the proof. For more general theorems of this
  type, see Knebusch [@bib:Knebusch1967].
]

#theorem[
  + Set $overline(Lambda) = Lambda slash rad Lambda tilde.equiv
    M_r (overline(Delta))$. There is a one-to-one correspondence
    $J -> overline(J)$ between maximal right ideals of $Lambda$ and those of
    $overline(Lambda)$. Here, $overline(J)$ is the image of $J$ in
    $overline(Lambda)$, and
    $Lambda slash J tilde.equiv overline(Lambda) slash overline(J)$. The module
    $Lambda slash J$ is a simple $Lambda$-module.
  + Let $x_1 = diag(pi_D, 1, dots, 1) in M_r (Delta)$. Then $x_1 Lambda$ is a
    maximal right ideal of $Lambda$, and its conjugates
    $
      {u dot x_1 Lambda dot u^(-1) : u in u(Lambda)}
    $
    give all of the maximal right ideals of $Lambda$.
  + #source(183)For $x in Lambda$, the right ideal $x Lambda$ is maximal if and
    only if the left ideal $Lambda x$ is maximal.
] <th:complete-local-maximal-right-ideals>

#proof[
  Each maximal right ideal $J$ of $Lambda$ contains $rad Lambda$, by
  @th:radical-maximal-left-ideals and @cor:radical-left-right. Therefore
  $
    Lambda slash J tilde.equiv (Lambda slash rad Lambda) slash
    (J slash rad Lambda) = overline(Lambda) slash overline(J).
  $
  Since $J$ is maximal, $Lambda slash J$ is a simple $Lambda$-module, whence
  $overline(Lambda) slash overline(J)$ is a simple $overline(Lambda)$-module.
  Therefore $overline(J)$ is also maximal. Conversely for each maximal right
  ideal $Y$ of $overline(Lambda)$, the kernel of the epimorphism
  $Lambda -> overline(Lambda) slash Y$ is a maximal right ideal $J$ of $Lambda$
  such that $overline(J) = Y$. This proves (i).

  Next, we have
  $
    1 - overline(x)_1 = e_11 = diag(1, 0, dots, 0) in overline(Lambda),
  $
  whence
  $
    overline(Lambda) slash overline(x)_1 overline(Lambda)
    = overline(Lambda) slash (1 - e_11) overline(Lambda)
    tilde.equiv e_11 overline(Lambda).
  $
  But $e_11$ is a primitive idempotent in $overline(Lambda)$, so
  $e_11 overline(Lambda)$ is a simple $overline(Lambda)$-module. Thus
  $x_1 Lambda$ is a maximal right ideal of $Lambda$, as claimed. The same
  argument shows that $Lambda x_1$ is a maximal left ideal of $Lambda$.

  By @th:complete-local-maximal-orders, every maximal right ideal of $Lambda$
  has the form $x Lambda$ for some $x in Lambda$. As in
  @th:skewfield-matrix-diagonalization, choose $u, v in u(Lambda)$ so that
  $
    u x v = diag(pi_D^(a_1), dots, pi_D^(a_r)), quad
    0 <= a_1 <= dots.c <= a_r.
  $
  But if $0 <= b_i <= a_i$, $1 <= i <= r$, then
  $
    u x v dot Lambda = diag(pi_D^(a_1), dots, pi_D^(a_r)) dot Lambda
    subset diag(pi_D^(b_1), dots, pi_D^(b_r)) dot Lambda subset Lambda.
  $
  Since $x Lambda$ is maximal, so is $u x v dot Lambda$, because left
  multiplication by $u$ carries $Lambda$ onto itself, and carries $x Lambda$
  onto $u x v dot Lambda$. Hence we have $a_1 = dots.c = a_(r-1) = 0$,
  $a_r = 1$, and thus
  $
    u x v = diag(1, dots, 1, pi_D) = x_r,
  $
  say. But $x_r = t x_1 t'$ for some $t, t' in u(Lambda)$, and thus
  $u x v = t x_1 t'$, so
  $
    x Lambda = u^(-1) t dot x_1 Lambda
    = (u^(-1) t) dot x_1 Lambda dot (u^(-1) t)^(-1).
  $
  This completes the proof of (ii).

  Finally, let $x Lambda$ be maximal. By the above, we may write $x = u' x_1 v'$
  for some $u', v' in u(Lambda)$. Then $Lambda x = Lambda x_1 dot v'$, whence
  $Lambda x$ is a maximal left ideal of $Lambda$, as claimed. This proves the
  theorem.
]
