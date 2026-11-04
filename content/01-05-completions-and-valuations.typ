#import "main-defs.typ": *
#import "statements.typ": *

== Completions and valuations <sec:completions-and-valuations>

=== Completions <ss:completions>

We shall review, without proof for the most part, some elementary facts about
completions. The reader is referred to the standard references, listed at the
start of §~@sec:dedekind-domains, for details and proofs.

Let $K$ be a field with a valuation $phi$, topologized as in
§~@ss:localizations-valuations. Let $hat(K)$ denote the completion of $K$
relative to this topology; then $hat(K)$ is a field whose elements are
equivalence classes of Cauchy sequences of elements of $K$, two sequences being
_equivalent_ if their difference is a null sequence. The field $K$ is embedded
in $hat(K)$, and the valuation $phi$ extends to a valuation $hat(phi)$ on
$hat(K)$. The field $hat(K)$ is _complete_ relative to the topology induced by
$hat(phi)$, that is, every Cauchy sequence from $hat(K)$ has a limit in
$hat(K)$.
#idx("complete field")

If $phi$ is an archimedean valuation, then so is $hat(phi)$, and $hat(K)$ is a
complete field with respect to an archimedean valuation. The only possibilities
for $hat(K)$ are #source(77)$bold(R)$ (the real field) or $bold(C)$ (the complex
field), and in each case $hat(phi)$ is equivalent to the usual absolute value.

If $phi$ is non-archimedean, so also is $hat(phi)$; the two valuations have the
same value group, and the same residue class field (up to isomorphism). In
particular, let $R$ be a Dedekind domain with quotient field $K$, where
$K != R$, and let $P$ be a maximal ideal of $R$. The completion of $K$ with
respect to the $P$-adic valuation $phi_P$ on $K$ (see
§~@ss:localizations-valuations) will be denoted by $hat(K)_P$ (or just $hat(K)$,
if there is no danger of confusion). Call $hat(K)_P$ a _$P$-adic_ field, and its
elements _$P$-adic_ numbers. The discrete valuation $phi_P$ extends to a
discrete valuation $hat(phi)_P$ on $hat(K)_P$. We have already remarked that the
valuation ring of $phi_P$ is the localization $R_P$; let $hat(R)_P$ be the
valuation ring of $hat(phi)_P$. Every element of $hat(R)_P$ can be represented
by a Cauchy sequence from $R_P$ (or from $R$, for that matter). If $pi$ is a
prime element of $R_P$, then $pi$ is also a prime element of $hat(R)_P$. Let
$cal(S)$ temporarily denote a full set of residue class representatives in $R$
of the residue class field $overline(R) = R slash P$, with $0 in cal(S)$. Each
$x in hat(R)_P$ is uniquely expressible as
#idx("$P$-adic field")
$
  x = alpha_0 + alpha_1 pi + alpha_2 pi^2 + dots.c, quad alpha_i in cal(S),
$
and each $y in hat(K)_P$ is uniquely of the form $y = pi^k dot x$,
$k in bold(Z)$, where uniqueness is guaranteed by the condition that
$alpha_0 != 0$. (If $y = 0$, take $k = +infinity$).

We note that $K$ is _dense_ in $hat(K)_P$, that is, given any
$alpha in hat(K)_P$ and any $epsilon > 0$, there exists an element $a in K$ such
that
#idx("dense")
$
  hat(phi)_P (a - alpha) < epsilon.
$
Likewise $R$ is dense in $hat(R)_P$, and so also is $R_P$.

#theorem[
  + $hat(R)_P$ is a faithfully flat $R_P$-module.
  + For each $k >= 1$, there are $R$-isomorphisms
    $
      R slash P^k tilde.equiv R_P slash pi^k R_P tilde.equiv
      hat(R)_P slash pi^k hat(R)_P,
    $
    where $pi$ is a prime element of $R_P$.
] <th:completion-residues>

#proof[
  The first assertion is contained in @cor:completion-flat (see also
  Exercise~@exc:completion-faithfully-flat). The first part of (ii) is proved in
  @th:localization-residue-modules. Finally, the composition of maps
  $R_P -> hat(R)_P -> hat(R)_P slash pi^k hat(R)_P$ yields a map
  $lambda: R_P -> hat(R)_P slash pi^k hat(R)_P$, and $lambda$ is an epimorphism
  since $R_P$ is dense in $hat(R)_P$. Clearly
  $ker lambda = R_P inter pi^k hat(R)_P = pi^k R_P$, which completes the proof.
]

For any $R$-module $M$, let
$
  M_P = R_P times.o_R M, quad
  hat(M)_P = hat(R)_P times.o_R M tilde.equiv hat(R)_P times.o_(R_P) M_P.
$
Thus the passage from $M$ to $hat(M)_P$ can be accomplished in two steps:
localization (from $M$ to $M_P$), and completion (from $M_P$ to $hat(M)_P$). In
the second step, we #source(78)start with a discrete valuation ring $R_P$, and
pass to its completion $hat(R)_P$. We shall analyze this step in some detail
below.

#theorem[
  Let $R$ be a discrete valuation ring with prime element $pi$, quotient field
  $K$, and let $hat(R)$, $hat(K)$ denote completions.
  + For each finitely generated $R$-module $M$, the map
    $M -> hat(R) times.o_R M$ is an inclusion. Denote $hat(R) times.o_R M$ by
    $hat(R) M$ hereafter.
  + Let $V$ be a finite dimensional $K$-space, and set
    $hat(V) = hat(K) times.o_K V$. The formulas
    $
      T = hat(R) M, quad M = T inter V,
    $
    give a one-to-one inclusion-preserving correspondence between the set of
    full $R$-lattices $M$ in $V$, and the set of full $hat(R)$-lattices $T$ in
    $hat(V)$.
] <th:lattices-completion>

#proof[
  For (i), we note that $M$ is isomorphic to a direct sum of cyclic modules of
  the form $R slash pi^k R$, $k >= 0$, so it suffices to prove the result for
  $M = R slash pi^k R$. But then
  $M -> hat(R) times.o_R M = hat(R) slash pi^k hat(R)$ is surely monic (obvious
  when $k = 0$, and true for $k > 0$ by @th:completion-residues).

  To prove (ii), use bases! Suppose first that $M$ is a full $R$-lattice in $V$.
  We may write
  $
    M = dsum_(i=1)^n R x_i, quad V = dsum_(i=1)^n K x_i, quad
    hat(M) = dsum_(i=1)^n hat(R) x_i,
  $
  where $n = (V : K)$. Then
  $
    hat(M) inter V = dsum (hat(R) inter K) x_i = dsum R x_i = M,
  $
  as desired.

  Conversely, let $T$ be a full $hat(R)$-lattice in $hat(V)$, and write
  $
    T = dsum_(i=1)^n hat(R) x_i, quad hat(V) = dsum_(i=1)^n hat(K) x_i, quad
    V = dsum_(i=1)^n K y_i
  $
  (note that $(V : K) = (hat(V) : hat(K))$). Then $y_i = sum sigma_(i j) x_j$,
  $sigma_(i j) in hat(K)$, $1 <= i <= n$, and $bold(S) = (sigma_(i j))$ is an
  invertible matrix over $hat(K)$. Choose $bold(T) = (tau_(i j))$ with entries
  in $K$ close to those of $bold(S)^(-1)$ (in the topology induced by the
  valuation); then $bold(T) bold(S)$ is a unit in the matrix ring
  $M_n (hat(R))$. Set
  $
    y'_i = sum tau_(i j) y_j = sum tau_(i j) sigma_(j k) x_k.
  $
  Then we have
  $
    T = dsum hat(R) x_i = dsum hat(R) y'_i, quad V = dsum K y'_i,
  $
  and so
  $
    T inter V = dsum (hat(R) inter K) y'_i = dsum R y'_i.
  $
  #source(79)Thus $T inter V$ is a full $R$-lattice in $V$ such that
  $hat(R)(T inter V) = T$. This completes the proof of the theorem.
]

We may now prove analogues of @th:lattice-intersection-of-localizations and
@th:lattice-from-local-data:

#theorem(major: true)[
  Let $R$ be a Dedekind domain with quotient field $K$, let $M$ be an
  $R$-lattice, and let $V = K M$. Let $P$ range over all maximal ideals of $R$.
  + We have
    $
      M = K M inter {inter.big_P hat(M)_P}.
    $
  + For each $P$, let there be given a full $hat(R)_P$-lattice $Y(P)$ in
    $hat(K)_P V$, such that $Y(P) = hat(M)_P$ a.e. Define
    $
      N = V inter {inter.big_P Y(P)}.
    $
    Then $N$ is a full $R$-lattice in $V$, and $hat(N)_P = Y(P)$ for all $P$.
] <th:lattice-from-completions>

#proof[
  By @th:lattices-completion, $M_P = K M inter hat(M)_P$ for each $P$. Assertion
  (i) now follows at once from @th:lattice-intersection-of-localizations. To
  prove (ii), set $X(P) = V inter Y(P)$ for each $P$. By
  @th:lattices-completion, $X(P)$ is a full $R_P$-lattice in $V$. Clearly
  $X(P) = V inter hat(M)_P = M_P$ a.e., and $N = inter.big_P X(P)$. By
  @th:lattice-from-local-data $N$ is a full $R$-lattice in $V$, and $N_P = X(P)$
  for all $P$. Therefore $hat(N)_P = hat(R)_P dot X(P) = Y(P)$ for all $P$, by
  @th:lattices-completion, and the theorem is proved.
]

We indicate the generalization of @th:lattice-from-completions to the case where
$R$ is a noetherian integrally closed domain. Recall that for each minimal prime
$P$ of such a domain $R$, the localization $R_P$ is a discrete valuation ring,
and so we may form its completion $hat(R)_P$ just as above.

#theorem[
  Let $M$ be a full $R$-lattice in a finite dimensional $K$-space $V$, where $R$
  is a noetherian integrally closed domain with quotient field $K$. Suppose that
  for each minimal prime $P$ of $R$, we are given an $hat(R)_P$-lattice $Y(P)$
  in $hat(V)_P$, such that $Y(P) = hat(M)_P$ a.e. Set
  $
    N = V inter {inter.big_P Y(P)}.
  $
  Then $N$ is a full $R$-lattice in $V$, $N$ is reflexive, and $hat(N)_P = Y(P)$
  for all $P$.
] <th:krull-lattice-from-completions>

#proof[
  The theorem follows readily from @th:krull-lattice-from-local-data and
  @th:lattices-completion.
]

=== Extensions of complete fields <ss:extensions-of-complete-fields>

Throughout this section, let $K$ be a field complete with respect to a valuation
$phi$, either archimedean or not, and let $tilde(K)$ be an algebraic closure of
$K$. Then (see references) we may extend $phi$ to a valuation $tilde(phi)$ on
$tilde(K)$, as follows: #source(80)each $a in tilde(K)$ lies in some field $L$
with $K subset L subset tilde(K)$, $(L : K)$ finite (for example, $L = K(a)$
will do). Set
$
  tilde(phi)(a) = {phi(N_(L slash K) a)}^(1 slash (L : K)).
$ <eq:extended-valuation>
Then we find that the value $tilde(phi)(a)$ is independent of the choice of $L$,
and that every finite extension of $K$ contained in $tilde(K)$ is complete with
respect to the valuation $tilde(phi)$.

When $phi$ is archimedean, there are only two possibilities:
#idx("archimedean valuation")
+ $K = bold(C) = tilde(K)$, $phi = tilde(phi)$
+ $K = bold(R)$, $tilde(K) = bold(C)$, $tilde(phi)$ extends $phi$,
where $phi$ and $tilde(phi)$ are the usual absolute values on $bold(R)$ or
$bold(C)$.

If $phi$ is non-archimedean, so is $tilde(phi)$. However, $tilde(phi)$ need not
be a discrete valuation, even if $phi$ is discrete.

We shall consider discrete valuations in more detail below, and for this purpose
let us adopt a more systematic notation. If $phi$ is a discrete valuation on
$K$, denote by $o_K$ its valuation ring, and by $p_K$ the maximal ideal of
$o_K$. Let $overline(o)_K = o_K slash p_K$ be the residue class field, and let
$p_K = pi_K dot o_K$, so $pi_K$ is a prime element of $o_K$. Let $v_K$ be the
_exponential valuation_ on $K$, defined by setting
$
  a o_K = p_K^(v_K (a)), quad a in K, quad a != 0,
$
and $v_K (0) = +infinity$.

Any finite extension $L$ of $K$ can be embedded in $tilde(K)$, and the
restriction of $tilde(phi)$ to $L$ gives a discrete valuation $psi$ which
extends $phi$. We define the _ramification index_ $e = e(L slash K)$ and
_residue class degree_ $f = f(L slash K)$ by the formulas #idx(
  "ramification index",
)#idx("residue class degree")
$
  v_L (pi_K) = e, quad (overline(o)_L : overline(o)_K) = f.
$

#theorem[
  Let $L$ be a finite extension of the complete field $K$, and keep the above
  notation. Then
  + $o_L$ is the integral closure of $o_K$ in $L$.
  + Both $e(L slash K)$ and $f(L slash K)$ are finite, and
    $
      e(L slash K) dot f(L slash K) = (L : K).
    $
  + For each $a in L$,
    $
      v_L (a) = f(L slash K)^(-1) dot v_K (N_(L slash K) a).
    $
  + Let $a_1, dots, a_f in o_L$ be such that
    $overline(o)_L = dsum overline(o)_K overline(a)_i$, and let
    $pi_0, pi_1, dots, pi_(e-1) in o_L$ be such that $v_L (pi_j) = j$,
    $0 <= j <= e - 1$, where $e = e(L slash K)$, $f = f(L slash K)$. Then the
    $e dot f$ elements ${a_i pi_j}$ form a free $o_K$-basis for $o_L$.
] <th:extensions-complete-fields>

For future use, we state

#theorem(title: [Hensel's Lemma])[
  Let $f(X) in o_K [X]$ and suppose that in $overline(o)_K [X]$ there is a
  factorization
  #source(81)
  $
    overline(f)(X) = u(X) v(X), quad u(X) "monic",
  $
  where $u(X)$ and $v(X)$ are relatively prime. Then there is a factorization in
  $o_K [X]$:
  $
    f(X) = g(X) h(X), quad g(X) "monic",
  $
  such that $overline(g) = u$, $overline(h) = v$.
  #idx("Hensel's Lemma", target: [@th:hensel])
] <th:hensel>

Recall that $L$ is an _unramified_ extension of $K$ if $e(L slash K) = 1$ and
$overline(o)_L$ is a separable extension of $overline(o)_K$. The study of
unramified extensions reduces at once to the study of separable extensions of
the residue class field $overline(o)_K$ by virtue of the following basic result
(see references):

#theorem[
  + There is a one-to-one inclusion-preserving correspondence between the set of
    fields $L$ such that
    $
      K subset L subset tilde(K), quad
      L = "finite unramified extension of" K,
    $
    and the set of fields $k$ finite separable over $overline(o)_K$. This
    correspondence assigns to each such field $L$ the field $k$ given by
    $k = overline(o)_L$.
  + If $L = K(a)$, where $a$ is a zero of a monic $f(X) in o_K [X]$ such that
    $overline(a)$ is a simple zero of $overline(f)(X)$, then $L$ is unramified
    over $K$, and
    $
      o_L = o_K [a], quad overline(o)_L = overline(o)_K (overline(a)), quad
      (L : K) = (overline(o)_L : overline(o)_K).
    $
    Conversely, every unramified extension $L$ of $K$ is of this form.
  + Given $k = overline(o)_K (xi)$, let $f(X) in o_K [X]$ be any monic
    polynomial such that $overline(f)(X) = minpol_(overline(o)_K) xi$. Then
    there exists a field $L = K(a) subset tilde(K)$ such that $L$ is unramified
    over $K$, and $overline(o)_L = k$, and further
    $
      f(X) = minpol_K a, quad overline(a) = xi "in" overline(o)_L.
    $
  + $L slash K$ is a galois extension if and only if
    $overline(o)_L slash overline(o)_K$ is a galois extension. If $G$ is the
    galois group of $L slash K$, then each $sigma in G$ induces an element
    $overline(sigma)$ in the galois group $overline(G)$ of
    $overline(o)_L slash overline(o)_K$. The map $sigma -> overline(sigma)$
    gives an isomorphism $G tilde.equiv overline(G)$.
] <th:unramified-extensions>

#corollary[
  Let $(E : K) < infinity$. There is a unique field $W$ which is maximal with
  respect to the properties
  $
    K subset W subset E, quad W "is unramified over" K.
  $
] <cor:inertia-field>

This field $W$ is the _inertia field_ of the extension $E slash K$; it is
characterized by the facts that $W slash K$ is unramified, and $overline(o)_W$
is the separable closure of $overline(o)_K$ in $overline(o)_E$, that is,
#idx("inertia field")
$
  overline(o)_W = {x in overline(o)_E : x "is separable over" overline(o)_K}.
$

#theorem[
  Suppose that the complete field $K$ has finite residue class field
  $overline(o)_K$, and let $q = card overline(o)_K$. Then for each positive
  integer $f$, there is a #source(82)unique unramified extension $W$ of $K$ such
  that $(W : K) = (overline(o)_W : overline(o)_K) = f$, namely, $W = K(omega)$
  for $omega$ a primitive $(q^f - 1)$-th root of 1 over $K$. Furthermore,
  $
    o_W = o_K [omega], quad overline(o)_W = overline(o)_K (overline(omega)).
  $
] <th:unramified-finite-residue>

#proof[
  There is a unique separable extension of $overline(o)_K$ of degree $f$, namely
  $overline(o)_K (xi)$, where $xi$ is a primitive $(q^f - 1)$-th root of 1 over
  $overline(o)_K$. Hence by @th:unramified-extensions there is a unique
  unramified extension $W$ of $K$ such that
  $(W : K) = (overline(o)_W : overline(o)_K) = f$. We need only show that
  $K(omega)$ is an unramified extension of $K$ such that $(K(omega) : K) = f$.
  However, $omega$ is a zero of the polynomial
  $
    f(X) = X^(q^f - 1) - 1 in o_K [X].
  $
  Since $overline(f)(X)$ has no repeated zeros, it follows from
  @th:unramified-extensions[(ii)] that $K(omega)$ is unramified over $K$.
  Further
  $
    f(X) = product (X - omega^i), quad
    overline(f)(X) = product (X - overline(omega)^i),
  $
  where $1 <= i <= q^f - 1$ in each product. Hence $overline(omega)$ is a
  primitive $(q^f - 1)$-th root of 1, so by @th:unramified-extensions[(ii)]
  $
    (K(omega) : K) = (overline(o)_K [overline(omega)] : overline(o)_K) = f.
  $
  This completes the proof of the theorem.
]

#corollary[
  Keep the notation of @th:unramified-finite-residue. Then $W slash K$ and
  $overline(o)_W slash overline(o)_K$ are galois extensions, with galois groups
  $G$, $overline(G)$ cyclic of order $f$. The group $G$ has generator
  $sigma: omega -> omega^q$, while $overline(G)$ is generated by
  $overline(sigma): overline(omega) -> overline(omega)^q$. Call $sigma$ the
  _Frobenius automorphism_ of the extension $W slash K$.
  #idx("Frobenius automorphism")
] <cor:frobenius>

#proof[
  It is well-known that $overline(G)$ is cyclic of order $f$ with generator
  $overline(sigma)$, since $overline(G)$ is the galois group of
  $overline(o)_K (overline(omega)) slash overline(o)_K$, and
  $overline(o)_K (overline(omega))$ is the splitting field of $f(X)$ over
  $overline(o)_K$. If $g(X) = minpol_(overline(o)_K) (overline(omega))$, then
  $
    g(X) = product_(i=0)^(f-1) (X - overline(omega)^(q^i)).
  $
  Therefore
  $
    minpol_K omega = product_(i=0)^(f-1) (X - omega^(q^i)),
  $
  and hence $sigma: omega -> omega^q$ is a generator of the group $G$.
]

The extreme opposites of unramified extensions are the completely ramified
extensions. Recall that $L$ is a _completely ramified_ extension of $K$ if
$overline(o)_L = overline(o)_K$, that is, $f(L slash K) = 1$. Such extensions
can be classified, as follows: an _Eisenstein polynomial_ is one of the form
#idx("completely ramified")#idx("Eisenstein polynomial")
#source(83)
$
  f(X) = X^n + a_1 X^(n-1) + dots.c + a_n in o_K [X],
$
where each $a_i in p_K$, and $a_n in.not p_K^2$. By
Exercise~@exc:eisenstein-irreducible, $f(X)$ is irreducible in $K[X]$.

#theorem[
  + Let $L$ be a completely ramified extension of $K$ of degree $n$. Then
    $minpol_K pi_L$ is an Eisenstein polynomial over $o_K$, and $L = K(pi_L)$.
  + Let $f(X)$ be an $n$-th degree Eisenstein polynomial over $o_K$, and let
    $L = K(alpha)$, where $minpol_K alpha = f(X)$. Then $L$ is completely
    ramified over $K$, $(L : K) = n$, and $alpha$ is a prime element of $o_L$.
    Furthermore, $o_L = o_K [alpha]$.
] <th:eisenstein-extensions>

The proof is straightforward (see references), and we omit it. We call
$L slash K$ an _Eisenstein extension_ if it is of the type described in
@th:eisenstein-extensions.
#idx("Eisenstein extension")

Now let $E$ be any finite extension of $K$, and suppose that the residue class
field $overline(o)_K$ is perfect, that is, $overline(o)_K$ has no inseparable
extensions. This certainly is the case when $overline(o)_K$ is a finite field.
If $W$ is the inertia field of the extension $E slash K$, then we have
$
  K subset W subset E, quad overline(o)_W = overline(o)_E, quad
  e(W slash K) = 1, quad f(E slash W) = 1, \
  f(W slash K) = f(E slash K), quad e(E slash W) = e(E slash K).
$
Thus the step from $K$ to $E$ is divided into an unramified step from $K$ to
$W$, followed by a completely ramified step from $W$ to $E$. We have seen that
$E$ is an Eisenstein extension of $W$, and if $overline(o)_K$ is finite, then
$W$ is a cyclotomic extension of $K$.

=== Extensions of valuations <ss:extensions-of-valuations>

Throughout this section, $K$ denotes a field with a valuation $phi$, archimedean
or not, and $hat(phi)$ the extension of $phi$ to the algebraic closure $Omega$
of the completion $hat(K)$, as in §~@ss:extensions-of-complete-fields. Given a
finite separable extension $L$ over $K$, we wish to determine all extensions of
the valuation $phi$ from $K$ to $L$. Each such extension determines an embedding
of $L$ in $Omega$ which preserves the embedding of $K$ in $hat(K)$. Two
embeddings $mu$, $mu'$ of $L$ in $Omega$ are called _equivalent_ if there exists
a $K$-isomorphism $sigma: mu(L) tilde.equiv mu'(L)$ such that $sigma mu = mu'$.
Let $mu_1, dots, mu_r$ be a full set of inequivalent isomorphisms of $L$ into
$Omega$ which preserve the embedding of $K$ in $hat(K)$. Let
$hat(L)_i = hat(K) dot mu_i (L)$, the composite of $hat(K)$ and $mu_i (L)$ in
$Omega$ (that is, the smallest subfield of $Omega$ containing both), and set
$n_i = (hat(L)_i : hat(K))$. Then (see references) there are precisely $r$
inequivalent valuations $psi_1, dots, psi_r$ of $L$ which extend $phi$, and
these are given by the formula
#idx("equivalence", "of embeddings")
$
  psi_i (a) = hat(phi)(mu_i (a))
  = {hat(phi)(N_(hat(L)_i slash hat(K)) (mu_i a))}^(1 slash n_i), quad
  1 <= i <= r.
$ <eq:extensions-of-valuation>

In order to obtain a full set of inequivalent embeddings of $L$ in $Omega$,
write $L = K(theta)$, $f(X) = minpol_K theta$, so $f(X)$ is a separable
polynomial. Factor #source(84)$f(X)$ into irreducible factors in $hat(K)[X]$:
$
  f(X) = product_(i=1)^r f_i (X), quad f_i (X) "irreducible", quad
  f_i (X) in hat(K)[X].
$
The ${f_i}$ are necessarily distinct, and we may choose elements
${theta_i} in Omega$ such that $f_i (theta_i) = 0$. Any $K$-isomorphism
$mu: L -> Omega$ must carry $theta$ into a $hat(K)$-conjugate of some $theta_i$,
and since we are interested in embeddings only up to equivalence, we may indeed
choose $mu_i$ so that $mu_i (theta) = theta_i$. In this way we obtain $r$
inequivalent embeddings $mu_1, dots, mu_r$ of $L$ in $Omega$, and for each $i$,
$1 <= i <= r$, we have
$
  hat(L)_i = hat(K)(theta_i), quad minpol_(hat(K)) theta_i = f_i (X).
$
Now
$
  L = K(theta) tilde.equiv K[X] slash (f(X)),
$
and thus
$
  hat(K) times.o_K L tilde.equiv hat(K)[X] slash (f(X)) tilde.equiv
  dsum_(i=1)^r hat(K)[X] slash (f_i (X)) tilde.equiv dsum_(i=1)^r hat(L)_i.
$
Hence for each $a in L$, we have
$
  charpol_(L slash K) a = product_(i=1)^r charpol_(hat(L)_i slash hat(K))
  mu_i (a),
$ <eq:char-pol-local-product>
since $a$ acts on $hat(K) times.o_K L$ just as $sum mu_i (a)$ acts on
$dsum hat(L)_i$. In particular, we obtain from @eq:char-pol-local-product the
important formulas
$
  T_(L slash K) a = sum_i T_(hat(L)_i slash hat(K)) mu_i (a), quad
  N_(L slash K) a = product_i N_(hat(L)_i slash hat(K)) mu_i (a).
$
Briefly, _global trace is the sum of local traces, and global norm the product
of local norms._

Suppose now that $R$ is a Dedekind domain with quotient field $K$, and $S$ the
integral closure of $R$ in $L$. For each maximal ideal $P$ of $R$, let
$
  P dot S = product_(i=1)^r P_i^(e_i)
$
be the factorization of $P dot S$ into a product of powers of distinct maximal
ideals ${P_i}$ of $S$. Then there are precisely $r$ inequivalent valuations
$psi_1, dots, psi_r$ on $L$ which extend the $P$-adic valuation $phi_P$ on $K$,
obtained by choosing $psi_i$ to be the $P_i$-adic valuation on $L$. The fields
$hat(L)_i$ defined above are precisely the $P_i$-adic completions of $L$, and we
have
$
  n_i = (hat(L)_i : hat(K)_P) = e_i f_i, quad
  e_i = e(P_i, L slash K) = e(hat(L)_i slash hat(K)_P), \
  f_i = f(P_i, L slash K) = f(hat(L)_i slash hat(K)_P), quad 1 <= i <= r.
$

#source(85)If $K$ is a global field, so that the residue class fields
$R slash P$, $S slash P_i$ are finite, we may _normalize_ the $P$-adic valuation
$phi_P$ of $K$, and the $P_i$-adic valuation $phi_(P_i)$ of $L$, by setting
$
  phi_P (a) = cal(N)(P)^(-v_P (a)), quad
  phi_(P_i) (b) = cal(N)(P_i)^(-v_(P_i) (b)), quad a in K, quad b in L,
$
where
$
  cal(N)(P) = card R slash P, quad
  cal(N)(P_i) = card S slash P_i = cal(N)(P)^(f_i).
$
In this case, $phi_(P_i) = phi_P^(n_i)$ on $K$, so $phi_(P_i)^(1 slash n_i)$ is
the valuation on $hat(L)_i$ which extends $phi_P$ on $hat(K)_P$. Thus
$
  phi_(P_i) (y) = phi_P (N_(hat(L)_i slash hat(K)_P) y), quad
  y in hat(L)_i.
$
Hence for $a in L$,
$
  phi_P (N_(L slash K) a)
  = product_(i=1)^r phi_P (N_(hat(L)_i slash hat(K)) mu_i a)
  = product_(i=1)^r phi_(P_i) (a), quad a in L.
$
(This also holds if $P$ is archimedean, with the standard normalizations of
$phi_P$, $phi_(P_i)$ as in §~@ss:global-fields).

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $P$ be a maximal ideal of the Dedekind domain $R$, and let
  $
    f(X) = X^n + a_1 X^(n-1) + dots.c + a_n in R[X],
  $
  where each $a_i in P$, and $a_n in.not P^2$. (Call $f$ an _Eisenstein
  polynomial_). Show that $f(X)$ is irreducible in $K[X]$.
  #hint[@exc:eisenstein-irreducible][By Gauss' Lemma, it suffices to show that
    $f(X)$ is irreducible in $R[X]$. Let bars denote passage to
    $R slash P = overline(R)$. If $f = g h$ in $R[X]$, then
    $X^n = overline(f) = overline(g) dot overline(h)$ in $overline(R)[X]$, so
    $g(0), h(0) in P$, whence $a_n in P^2$.] <hint:eisenstein-irreducible>
] <exc:eisenstein-irreducible>

#exercise[
  Let $R$ be a complete discrete valuation ring, $overline(R)$ its residue class
  field, and suppose that $overline(R)$ is a finite field with $q$ elements.
  Using Hensel's Lemma @th:hensel, show that the polynomial $X^(q-1) - 1$ splits
  into $q - 1$ distinct linear factors in $R[X]$.
] <exc:roots-of-unity-complete>

#exercise[
  Let $hat(R)$ be the $P$-adic completion of the discrete valuation ring $R$.
  Prove directly#footnote[That is, without using
    @cor:completion-faithfully-flat.] <fn:directly> that $hat(R)$ is faithfully
  flat as $R$-module. #hint[@exc:completion-faithfully-flat][We show that
    $hat(R)$ is $R$-flat, that is, for each inclusion $i: L subset M$ of
    $R$-modules, the map $1 times.o i: hat(R) times.o L -> hat(R) times.o M$ is
    also an inclusion, where $times.o$ is over $R$. If $(1 times.o i) u = 0$,
    this equation in $hat(R) times.o M$ holds as a consequence of finitely many
    defining relations of the tensor product $hat(R) times.o M$. Hence it
    suffices to prove that $i': R' times.o L -> R' times.o M$ is monic, where
    $R'$ is some finitely generated $R$-submodule of $hat(R)$. But then $R'$ is
    $R$-free, and so $i'$ is clearly monic.

    To show that $hat(R)$ is faithfully flat, we show that
    $hat(R) times.o M != 0$ if $M != 0$. Choose any nonzero $m in M$. Since
    $hat(R)$ is $R$-flat, $hat(R) times.o R m$ is a submodule of
    $hat(R) times.o M$. But $R m tilde.equiv R slash J$, $J = ann_R m < R$, and
    then
    $
      hat(R) times.o (R slash J) tilde.equiv hat(R) slash J hat(R) != 0.
    $] <hint:completion-faithfully-flat>
] <exc:completion-faithfully-flat>

#exercise[
  Let $hat(R)_P$ be the $P$-adic completion of a Dedekind domain $R$. Prove
  directly#footnote(<fn:directly>) that #source(86)$hat(R)_P$ is $R$-flat.
  #hint[@exc:dedekind-completion-flat][Flatness is transitive, since
    $
      hat(R)_P times.o_R dot = hat(R)_P times.o_(R_P) (R_P times.o_R dot).
    $
    But $R_P$ is $R$-flat, and $hat(R)_P$ is $R_P$-flat, by
    Exercise~@exc:completion-faithfully-flat.]
  <hint:dedekind-completion-flat>
] <exc:dedekind-completion-flat>

#exercise[
  Does @th:lattices-completion[(i)] remain true without the hypothesis that $M$
  be finitely generated?
] <exc:completion-not-finitely-generated>

#exercise[
  Keeping the notation of @th:lattices-completion, show that if $T$ is an
  $hat(R)$-lattice of $hat(V)$ with $rank_(hat(R)) T < (V : K)$, then it may
  happen that $T inter V = 0$.
] <exc:non-full-lattice-intersection>

#exercise[
  Let $R$ be a discrete valuation ring with maximal ideal $P = pi R$, and let
  $hat(R)$ be its $P$-adic completion. For $M$ a finitely generated $R$-module,
  we set $hat(M) = hat(R) times.o_R M$. Prove
  + $M slash pi^k M tilde.equiv hat(M) slash pi^k hat(M)$, $k >= 1$.
  + $M inter pi^k hat(M) = pi^k M$, $k >= 0$, where we view $M$ as a submodule
    of $hat(M)$ as in @th:lattices-completion.
  #hint[@exc:completion-residue-modules][We can express $M$ as a direct sum of
    cyclic modules of the form $R slash P^n$, $n >= 0$, and it suffices to prove
    the results when $M = R slash P^n$. For $M = R$, (i) follows from
    @th:completion-residues, while (ii) is clear. For $M = R slash P^n$,
    $n >= 1$, we have $hat(M) tilde.equiv hat(R) slash P^n hat(R)$, so
    $M tilde.equiv hat(M)$ by @th:completion-residues. Identifying $M$ with
    $hat(M)$, it is then obvious that (i) and (ii) hold true.]
  <hint:completion-residue-modules>
] <exc:completion-residue-modules>
