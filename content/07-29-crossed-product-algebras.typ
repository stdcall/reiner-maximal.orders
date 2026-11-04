#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/common.typ": ladder
#import "diagrams/07-29-crossed-product-algebras.typ": (
  composite-fields, inflation-tower, sylow-fields,
)

== Crossed-product algebras <sec:crossed-product-algebras>

Throughout this section, $L$ denotes a finite galois extension of the field $K$,
with galois group $Gal(L slash K)$, and $E$ denotes an arbitrary field
containing $K$. Let $D$ be a skewfield with center $K$. We set $E^* = E - {0}$,
the multiplicative group of nonzero elements of $E$.

In §~@sec:finite-residue-class-field we were concerned with the special case
where $K$ is a complete field with a finite residue class field. We showed how
to construct a skewfield $D$ with center $K$ and given index $n$. Recall that we
start with a field $W supset K$ such that $Gal(W slash K)$ is a cyclic group of
order $n$, with generator $sigma$ (say). Then
$
  D = dsum_(j=0)^(n-1) W z^j, quad z^j alpha = sigma^j (alpha) z^j, quad
  alpha in W, quad 0 <= j <= n - 1,
$
and $z^n in W^*$. Here, $W$ is a maximal subfield of $D$, and $D$ has a
$W$-basis whose elements correspond to those of $Gal(W slash K)$. This
correspondence is such that
$
  z^j alpha z^(-j) = sigma^j (alpha), quad alpha in W, quad 0 <= j <= n - 1.
$
Further, the set of basis elements ${z^j}$ is closed under multiplication, apart
#source(251)from constant factors from $W^*$. This construction is a special
case of the extremely important concept of crossed-product algebras, which we
proceed to define.

Returning to the case of arbitrary $K$, let $G = Gal(L slash K)$. We shall
define an algebra $A = dsum_(sigma in G) L u_sigma$, having as $L$-basis a set
of symbols ${u_sigma : sigma in G}$. These symbols are to be manipulated
according to the formulas
$
  u_sigma dot x = sigma(x) dot u_sigma, quad u_sigma u_tau = f_(sigma, tau)
  u_(sigma tau), quad x in L, quad sigma, tau in G,
$ <eq:crossed-product-relations>
where each $f_(sigma, tau) in L^*$. Note that $K$ is contained in the center of
$A$, but that $L$ is not (if $L != K$), since the $u_sigma$'s need not
centralize $L$. The $K$-algebra $A$ will be associative if and only if
$u_rho (u_sigma u_tau) = (u_rho u_sigma) u_tau$ for all $rho, sigma, tau in G$,
or equivalently, if and only if
$
  rho(f_(sigma, tau)) dot f_(rho, sigma tau) = f_(rho, sigma) dot
  f_(rho sigma, tau), quad rho, sigma, tau in G.
$ <eq:factor-set-condition>
A map $f: G times G -> L^*$ satisfying @eq:factor-set-condition is a _factor
set_#idx("factor set") from $G$ to $L^*$. Given such an $f$, the algebra $A$
constructed above is called a _crossed-product algebra_#idx(
  "crossed-product algebra",
), and is denoted by $(L slash K, f)$.

If $f$ and $g$ are factor sets, so is $f g$, where by definition
$
  (f g)_(sigma, tau) = f_(sigma, tau) dot g_(sigma, tau), quad sigma, tau in G.
$
Now let $A = dsum L u_sigma$ as above, let ${c_sigma : sigma in G}$ be any set
of elements of $L^*$, and put $v_sigma = c_sigma u_sigma$, $sigma in G$. Then
$A = dsum L v_sigma$, and
$
  v_sigma dot x = sigma(x) dot v_sigma, quad v_sigma v_tau = g_(sigma, tau)
  v_(sigma tau), quad x in L, quad sigma, tau in G,
$
where
$
  g_(sigma, tau) = c_sigma dot sigma(c_tau) dot c_(sigma tau)^(-1) dot
  f_(sigma, tau), quad sigma, tau in G.
$
The map $delta c: G times G -> L^*$, given by
$
  (delta c)_(sigma, tau) = c_sigma dot sigma(c_tau) dot c_(sigma tau)^(-1),
  quad sigma, tau in G,
$ <eq:principal-factor-set>
is easily found to be a factor set, hereafter called a _principal_ factor
set#idx("principal factor set"). We have thus shown that $g = (delta c) dot f$,
and that
$
  (L slash K, f) tilde.equiv (L slash K, (delta c) dot f)
$ <eq:equivalent-factor-sets-isomorphic>
for each $c: G -> L^*$.

A few definitions are in order. The _trivial_ factor set#idx(
  "trivial factor set",
) has all values equal to 1. The collection of all factor sets from $G$ to $L^*$
is a multiplicative group $Z^2 (G, L^*)$, and the collection of all principal
factor sets is a subgroup $B^2 (G, L^*)$. We set
$
  H^2 (G, L^*) = Z^2 (G, L^*) slash B^2 (G, L^*),
$
the _second cohomology group_#idx("cohomology group")#footnote[See
  Exercise~@exc:factor-sets-cocycles.] of $G$ with coefficients in $L^*$. Call
$f, g in Z^2 (G, L^*)$ #source(252)_equivalent_#idx(
  "equivalence",
  "of factor sets",
) if $f$, $g$ have the same image $[f]$ in $H^2 (G, L^*)$, that is, if
$g = (delta c) f$ for some $c$.

It is easily shown that every factor set $g$ is equivalent to a _normalized_
factor set $f$ satisfying #idx("normalized factor set")
$
  f_(sigma, 1) = f_(1, sigma) = 1, quad sigma in G.
$ <eq:normalized-factor-set>
(See Exercise~@exc:normalized-factor-set). By
@eq:equivalent-factor-sets-isomorphic, equivalent factor sets yield isomorphic
crossed-product algebras. In particular, if $(L slash K, f) = dsum L u_sigma$ is
a crossed-product algebra in which $f$ is normalized, then $u_1$ is the unity
element of the ring $(L slash K, f)$, and each $u_sigma$ is a unit in this ring.
We shall always identify $L$ with the subring $L u_1$ of $(L slash K, f)$. Even
when $f$ is not necessarily normalized, the preceding remarks show that each
$u_sigma$ must be a unit in $(L slash K, f)$.

#theorem[
  For each factor set $f: G times G -> L^*$, the crossed-product algebra
  $A = (L slash K, f)$ is a central simple $K$-algebra. The field $L$ is its own
  centralizer in $A$, and is a maximal subfield of $A$. If $g$ is another factor
  set, then there exists a $K$-isomorphism
  $
    (L slash K, f) tilde.equiv (L slash K, g)
  $
  if and only if $f$ is equivalent to $g$.
] <th:crossed-product-central-simple>

#proof[
  Without loss of generality, we may assume that both $f$ and $g$ are
  normalized. Identify $L$ with $L u_1 subset A$. We leave it as an exercise to
  check that $K$ is the center of $A$, and that every element of $A$ which
  commutes with each $x in L$ must lie in $L$. Thus $L$ is its own centralizer
  in $A$, and is therefore a maximal subfield of $A$.

  To prove that $A$ is simple, let $X$ be a nonzero two-sided ideal of $A$, and
  let
  $
    x = a_(sigma_1) u_(sigma_1) + dots.c + a_(sigma_r) u_(sigma_r) in X, quad
    x != 0,
  $
  with $r$ minimal. If $r > 1$, choose $b in L$ with
  $sigma_1 (b) != sigma_2 (b)$. Then $x - sigma_1 (b)^(-1) x b$ is a shorter
  nonzero element of $X$. This is impossible, so necessarily $r = 1$, and $X$
  contains a unit $a_(sigma_1) u_(sigma_1)$ of $A$. Therefore $X = A$, which
  shows that $A$ is a central simple $K$-algebra, as claimed.

  Now let $B = dsum L v_sigma$, where the ${v_sigma}$ multiply according to the
  factor set $g$. Any $K$-algebra isomorphism $phi.alt: A tilde.equiv B$ must
  preserve identity elements, so $phi.alt(u_1) = v_1$. Therefore
  $phi.alt(L u_1) = L' v_1$, where $L'$ is a field $K$-isomorphic to $L$. Let
  $u'_sigma = phi.alt(u_sigma)$, $sigma in G$; then
  $phi.alt(L u_sigma) = L' v_1 dot u'_sigma = L' u'_sigma$. Therefore
  $
    B = dsum_(sigma in G) L' u'_sigma, quad u'_sigma dot phi.alt(x) =
    phi.alt(sigma x) dot u'_sigma, quad u'_sigma u'_tau =
    phi.alt(f_(sigma, tau)) u'_(sigma tau),
  $ <eq:crossed-product-image>
  for $x in L$, $sigma, tau in G$. On the other hand, $L' v_1$ and $L v_1$ are
  $K$-isomorphic simple subalgebras of $B$, so by the Skolem–Noether Theorem
  @th:skolem-noether, there is an #source(253)inner automorphism $theta$ of $B$
  such that $theta(phi.alt(x)) = x$, $x in L$. Applying $theta$ to equations
  @eq:crossed-product-image and setting $w_sigma = theta(u'_sigma)$,
  $sigma in G$, we obtain
  $
    B = dsum L w_sigma, quad w_sigma dot x = sigma(x) dot w_sigma, quad
    w_sigma dot w_tau = f_(sigma, tau) w_(sigma tau).
  $
  But for each $sigma in G$, $w_sigma v_sigma^(-1)$ commutes with each $x in L$.
  Since $L$ is its own centralizer in $B$, this gives
  $w_sigma = c_sigma v_sigma$ for some $c_sigma in L$. The ${w_sigma}$ are an
  $L$-basis for $B$, so each $c_sigma != 0$. Clearly we have $f = (delta c) g$,
  so $f$ is equivalent to $g$. This establishes the theorem, since we have
  previously remarked that $A tilde.equiv B$ whenever $f$ is equivalent to $g$.
]

#corollary[
  Let $n = (L : K)$. Then $(L slash K, f) tilde.equiv M_n (K)$ if and only if
  $f$ is equivalent to the trivial factor set.
] <cor:crossed-product-trivial-factor-set>

#proof[
  We need only show that $(L slash K, 1) tilde.equiv M_n (K)$, where 1 denotes
  the trivial factor set. Now
  $
    (L slash K, 1) = dsum_(sigma in G) L u_sigma, quad u_sigma dot x =
    sigma(x) u_sigma, quad u_sigma u_tau = u_(sigma tau),
  $
  for $x in L$, $sigma, tau in G$. For $x in L$, let $x'$ denote left
  multiplication by $x$ acting on $L$. Then there is an algebra homomorphism
  $
    psi: (L slash K, 1) -> Hom_K (L, L), quad "where" quad x u_sigma -> x'
    compose sigma.
  $
  The kernel is a two-sided ideal of the simple algebra $(L slash K, 1)$, hence
  is zero. Then $psi$ is monic, and must be an isomorphism since both
  $(L slash K, 1)$ and $Hom_K (L, L)$ have $K$-dimension $n^2$.
]

#example(numbered: false)[
  Let $K = bold(Q)$, $L = bold(Q)(i)$, $i^2 = -1$. Then $G = Gal(L slash K)$ is
  cyclic of order 2; with generator $sigma$, where $sigma(a + b i) = a - b i$,
  $a, b in bold(Q)$. Let $f: G times G -> L^*$ be the factor set given by
  $
    f_(1, 1) = f_(sigma, 1) = f_(1, sigma) = 1, quad f_(sigma, sigma) = -1.
  $
  Then $A = (L slash K, f) = L u_1 plus.o L u_sigma$, where $u_1$ is the unity
  element of $A$, and where
  $
    u_sigma dot x = sigma(x) u_sigma, quad u_sigma^2 = -1, quad x in L.
  $
  Thus $A$ is isomorphic to the quaternion algebra
  $bold(Q) plus.o bold(Q) i plus.o bold(Q) j plus.o bold(Q) k$ over $bold(Q)$,
  by identifying $bold(Q) plus.o bold(Q) i$ with $L$, and $j$ with $u_sigma$.
  #idx("quaternion skewfield")

  On the other hand, if we had chosen $f$ normalized, with
  $f_(sigma, sigma) = +1$, then $(L slash K, f) tilde.equiv M_2 (K)$ by
  @cor:crossed-product-trivial-factor-set. This completes the example.
]

#theorem[
  Let $G = Gal(L slash K)$, and let $f$, $g$ be factor sets from $G$ to $L^*$.
  Then there is a similarity of $K$-algebras
  $
    (L slash K, f) times.o_K (L slash K, g) tilde.op (L slash K, f g).
  $
] <th:crossed-product-tensor>

#proof[
  #source(254)Let $C = A times.o_K B$, where
  $
    A = (L slash K, f) = dsum L u_sigma, quad B = (L slash K, g) =
    dsum L v_sigma.
  $
  Then $C$ is a central simple $K$-algebra, by @th:tensor-central-simple. We
  shall find an idempotent $e in L times.o_K L subset C$ such that
  $e C e tilde.equiv (L slash K, f g)$. This will yield the desired result,
  since $C tilde.op e C e$ by Exercise~@exc:idempotent-corner-similar.

  To begin with, we observe that the subfields $L times.o 1$ and $1 times.o L$
  of $L times.o_K L$ commute elementwise. Since $L$ is separable over $K$, there
  exists an $a in L$ such that $L = K(a)$; then $f(X) = minpol_K a$ has degree
  $n$, where $n = (L : K)$. Now define
  $
    e = product (a times.o 1 - 1 times.o sigma a) slash product (a - sigma a)
    times.o 1,
  $
  where these products are taken over all $sigma in G - {1}$. Note that the
  denominator is not zero, since $a != sigma a$ for each $sigma in G - {1}$. The
  numerator is also different from zero in $L times.o_K L$, since the elements
  ${a^r times.o 1 : 0 <= r <= n - 1}$ are linearly independent over
  $1 times.o L$. Thus $e != 0$ in $L times.o_K L$.

  Next we note that $f(X) = (X - a) dot product (X - sigma a)$, where $sigma$
  ranges over $G - {1}$. Therefore
  $
    (a times.o 1 - 1 times.o a) dot product (a times.o 1 - 1 times.o sigma a) =
    f(a times.o 1) = 0.
  $
  This shows that $(1 times.o a) e = (a times.o 1) e$ in $L times.o L$.
  Therefore by induction on $r$, it follows that
  $
    (a^r times.o 1) e = (1 times.o a^r) e, quad r >= 0.
  $
  Since $L = dsum_(r=0)^(n-1) K a^r$, and multiplication in $L times.o L$ is
  commutative, we obtain
  $
    (x times.o 1) e = e(x times.o 1) = e(1 times.o x) = (1 times.o x) e, quad
    x in L.
  $ <eq:idempotent-diagonal>
  Consequently
  $
    e^2 & = e dot product (a times.o 1 - 1 times.o sigma a) slash product
          (a - sigma a) times.o 1 \
        & = e dot product ((a - sigma a) times.o 1) slash product (a - sigma a)
          times.o 1 \
        & = e.
  $
  Thus $e$ is an idempotent in $L times.o_K L$.

  It remains for us to prove that $e C e tilde.equiv (L slash K, f g)$. We have
  $
    e C e & = sum_(sigma, tau in G) e(L times.o L) dot (u_sigma times.o v_tau)
            e \
          & = sum_(sigma, tau) e(L times.o 1) e dot e(1 times.o L) e dot
            e(u_sigma times.o v_tau) e.
  $
  But $e(1 times.o L) e = e(L times.o 1) e$ by @eq:idempotent-diagonal, and
  $e(L times.o 1) e = L'$ is a field #source(255)$K$-isomorphic to $L$. Let us
  compute $e(u_sigma times.o v_tau) e$, by using the formulas
  $
    u_sigma dot x = sigma(x) u_sigma, quad v_tau dot x = tau(x) dot v_tau,
    quad x in L, quad sigma, tau in G.
  $
  Then
  $
    e(u_sigma times.o v_tau) e & = (u_sigma times.o v_tau) dot brace.l
                                 product (sigma^(-1) a times.o 1 - 1 times.o
                                   tau^(-1) rho a) \
                               & quad slash product (sigma^(-1) a - sigma^(-1)
                                   rho a) times.o 1 brace.r dot e,
  $
  where $rho$ ranges over all elements of $G - {1}$. From
  @eq:idempotent-diagonal, we obtain
  $
    e(u_sigma times.o v_tau) e & = (u_sigma times.o v_tau) dot e dot product
                                 (sigma^(-1) a - tau^(-1) rho a) times.o 1 \
                               & quad slash product (sigma^(-1) a - sigma^(-1)
                                   rho a) times.o 1.
  $ <eq:idempotent-conjugates>
  If $sigma != tau$, then $sigma^(-1) a - tau^(-1) rho a = 0$ for
  $rho = tau sigma^(-1) in G - {1}$, and hence $e(u_sigma times.o v_tau) e = 0$.
  On the other hand, when $sigma = tau$ we obtain
  $e(u_sigma times.o v_sigma) e = (u_sigma times.o v_sigma) e$. An analogous
  argument proves that
  $e(u_sigma times.o v_sigma) e = e(u_sigma times.o v_sigma)$.

  We have now shown that
  $
    e C e = dsum_(sigma in G) L' w_sigma,
  $
  where
  $
    L' = e(L times.o 1) e, quad w_sigma = e(u_sigma times.o v_sigma) e, quad
    sigma in G,
  $
  and have also shown that
  $
    w_sigma = (u_sigma times.o v_sigma) e = e(u_sigma times.o v_sigma), quad
    sigma in G.
  $
  Clearly $Gal(L' slash K) tilde.equiv G$, and we have for $x in L$,
  $
    w_sigma dot e(x times.o 1) e = e(u_sigma times.o v_sigma)(x times.o 1) e =
    e(sigma x times.o 1) e dot w_sigma.
  $
  Thus, conjugation by $w_sigma$ acts as $sigma$ on $L'$. Further, for
  $sigma, tau in G$,
  $
    w_sigma dot w_tau & = e(u_sigma u_tau times.o v_sigma v_tau) e =
                        e(f_(sigma, tau) u_(sigma tau) times.o g_(sigma, tau)
                          v_(sigma tau)) e \
                      & = e(f_(sigma, tau) g_(sigma, tau) times.o 1) e dot
                        w_(sigma tau).
  $
  Thus the $w$'s multiply according to the factor set $f g$. This proves that
  $e C e tilde.equiv (L' slash K, f g)$, and establishes the theorem.
]

We are now in a position to relate crossed-product algebras with the Brauer
group. We have denoted by $B(L slash K)$ the subgroup of the Brauer group $B(K)$
consisting of all classes of central simple $K$-algebras split by $L$.

#theorem(major: true)[
  Let $L$ be a finite galois extension of $K$, with galois group $G$. Then
  $
    H^2 (G, L^*) tilde.equiv B(L slash K),
  $
  and the isomorphism is given by mapping $[f] in H^2 (G, L^*)$ onto the class
  $[(L slash K, f)] in B(L slash K)$.
] <th:crossed-products-brauer-group>

#proof[
  #source(256)The indicated map is a well-defined monomorphism of groups, by
  @th:crossed-product-central-simple and @th:crossed-product-tensor. To show
  that the map is epic, let $A'$ be any central simple $K$-algebra which is
  split by $L$. Then by @rem:self-centralizing-maximal-subfield there exists a
  central simple $K$-algebra $A tilde.op A'$, such that $L$ is a
  self-centralizing maximal subfield of $A$, and
  $
    (A : K) = n^2, quad "where" quad n = (L : K).
  $
  Of course $[A'] = [A]$ in $B(L slash K)$.

  For each $sigma in G$, the map $sigma: L -> L$ is a $K$-isomorphism of simple
  subalgebras of $A$. Hence by the Skolem–Noether Theorem @th:skolem-noether,
  there exists $u_sigma in u(A)$ such that
  $
    u_sigma x u_sigma^(-1) = sigma(x), quad x in L, quad sigma in G.
  $

  In order to prove that $A = dsum_(sigma in G) L u_sigma$, it suffices to show
  that the right hand expression is a direct sum, for then both sides will have
  $K$-dimension $n^2$. If the sum is _not_ direct, let
  $
    s = a_(sigma_1) u_(sigma_1) + dots.c + a_(sigma_k) u_(sigma_k) = 0, quad
    a_(sigma_i) in L^*,
  $
  be a relation with minimal $k$. Surely $k > 1$, since each $u_sigma in u(A)$.
  Choosing $b in L^*$ such that $sigma_1 (b) != sigma_2 (b)$, one easily checks
  that
  $
    sigma_1 (b) s - s b = 0
  $
  gives a shorter nontrivial relation connecting
  $u_(sigma_2), dots, u_(sigma_k)$. This is a contradiction, and establishes the
  formula $A = dsum L u_sigma$.

  We already know that
  $
    u_sigma dot x = sigma(x) dot u_sigma, quad x in L, quad sigma in G.
  $
  Suppose now that $sigma, tau in G$. Then the preceding equation shows that
  $u_sigma u_tau u_(sigma tau)^(-1)$ commutes with each $x in L$. Since $L$ is
  its own centralizer in $A$, we obtain
  $
    u_sigma u_tau = f_(sigma, tau) u_(sigma tau), quad f_(sigma, tau) in L^*.
  $
  The associativity of multiplication in $A$ implies that $f: G times G -> L^*$
  is a factor set, and thus we have shown that $A tilde.equiv (L slash K, f)$
  for some $f$. This completes the proof of the theorem.
]

The preceding theorem shows that every class in the Brauer group $B(K)$ is
represented by a crossed-product algebra over $K$. Hence every skewfield $D$
with center $K$, such that $(D : K)$ is finite, is similar to some
crossed-product algebra $(L slash K, f)$. However, as shown by Amitsur
[@bib:Amitsur1972], there exist skewfields #source(257)$D$ which are not
isomorphic to crossed-product algebras. (See also Schacher–Small
[@bib:Schacher1973]).

Let us next establish some results on change of fields in crossed-product
algebras.

#theorem[
  Let $L slash K$ be a finite galois extension, and $E slash K$ an arbitrary
  extension. Then
  $
    E times.o_K (L slash K, f) tilde.op (E L slash E, f'),
  $
  where $f'$ is obtained from $f$ by restriction, as described below.
] <th:crossed-product-base-change>

#proof[
  Let $E L$ be the composite of the fields $E$ and $L$, in some extension field
  of $K$ containing both $E$ and $L$. Let $F = E inter L$. By galois theory, we
  know that $E L slash E$ is a finite galois extension, and we have a diagram
  $
    #composite-fields[$H = Gal(E L slash E) tilde.equiv Gal(L slash F)
    subset Gal(L slash K) = G.$]
  $
  Thus each factor set $f: G times G -> L^*$ restricts to a factor set
  $f': H times H -> L^*$, and so we may construct crossed-product algebras
  $(L slash F, f')$ and $(E L slash E, f')$. We shall prove
  #idx("restriction map")
  $
    F times.o_K (L slash K, f) tilde.op (L slash F, f'),
  $ <eq:crossed-product-restriction>
  $
    E times.o_F (L slash F, f') tilde.equiv (E L slash E, f').
  $ <eq:crossed-product-composite>
  Together these yield the assertion in the theorem, since
  $
    E times.o_K (L slash K, f) tilde.equiv E times.o_F (F times.o_K
      (L slash K, f)).
  $

  Let $F'$ be the centralizer of $F$ in the central simple $K$-algebra
  $A = (L slash K, f)$. By @cor:centralizer-tensor we have
  $
    F times.o_K A tilde.op F',
  $
  so @eq:crossed-product-restriction will be established as soon as we show that
  $
    F' tilde.equiv (L slash F, f').
  $
  Let $sum_(sigma in G) a_sigma u_sigma in F'$, where each $a_sigma in L$. Then
  for all $x in F$,
  $
    x dot sum a_sigma u_sigma = (sum a_sigma u_sigma) dot x = sum a_sigma
    sigma(x) u_sigma.
  $
  Hence whenever $a_sigma != 0$, we must have $sigma(x) = x$ for all $x in F$,
  that is, #source(258)$sigma in H = Gal(L slash F)$. This shows that
  $
    F' = dsum_(sigma in H) L u_sigma = (L slash F, f'),
  $
  so @eq:crossed-product-restriction is proved.

  Now let $B = (L slash F, f')$. The $F$-algebra homomorphism
  $
    E times.o_F L -> E L, quad x times.o y -> x y,
  $
  is an isomorphism (since the map is epic, and both sides have $E$-dimension
  $(L : F)$). Therefore
  $
    E times.o_F B = dsum_(sigma in H) (E times.o_F L)(1 times.o u_sigma)
    tilde.equiv dsum_(sigma in Gal(E L slash E)) E L dot v_sigma,
  $
  where the ${v_sigma}$ multiply according to the factor set $f'$. This proves
  @eq:crossed-product-composite, and establishes the theorem.
]

#theorem[
  Let $K subset L subset E$, where $L slash K$ and $E slash K$ are finite galois
  extensions. Then
  $
    (L slash K, f) tilde.op (E slash K, g),
  $
  as $K$-algebras, where $g$ is the _inflation_ of $f$, as described below.
] <th:crossed-product-inflation>

#proof[
  By galois theory, there is a diagram
  $
    #inflation-tower[
      $ & G = Gal(E slash K), quad H = Gal(E slash L), quad
        H normal G, \
      & overline(G) = G slash H tilde.equiv Gal(L slash K), \
      & r = (E : L), quad s = (L : K). $
    ]
  $
  Given a factor set $f: overline(G) times overline(G) -> L^*$, we define a
  factor set $g: G times G -> L^* subset E^*$ by the formula
  $
    g_(sigma, tau) = f_(overline(sigma), overline(tau)), quad sigma, tau in G,
  $
  where $overline(sigma)$ denotes the image of $sigma$ in $overline(G)$. Call
  $g$ the _inflation_ of $f$. #idx("inflation")

  Let us set
  $
    B = (L slash K, f) times.o_K M_r (K),
  $
  a central simple $K$-algebra split by $L$ (and hence also split by the field
  $E$ which contains $L$). Then
  $
    (L slash K, f) tilde.op B, quad (B : K) = (r s)^2, quad (E : K) = r s.
  $
  By @cor:self-centralizing-embedding, we know that $E$ can be embedded in $B$
  as a self-centralizing maximal subfield of $B$. We shall give a specific such
  embedding, and shall use it to prove that $B tilde.equiv (E slash K, g)$,
  where $g$ is the inflation of $f$. This will complete the proof of the
  theorem.

  #source(259)It follows from @cor:crossed-product-trivial-factor-set that there
  is an $L$-isomorphism
  $
    (E slash L, 1) tilde.equiv M_r (L).
  $
  We shall need to know an explicit form of this isomorphism. Let
  $E = dsum_(i=1)^r L e_i$, and for each $x in E$, let $T(x) in M_r (L)$
  describe the action of $x$ by left multiplication on the ${e_i}$. Thus
  $
    x(e_1, dots, e_r) = (e_1, dots, e_r) T(x), quad x in E.
  $
  On the other hand, each $rho in G$ may be viewed as an element of
  $Hom_K (E, E)$, and hence determines a matrix $P_rho in M_r (L)$ such that
  $
    (rho e_1, dots, rho e_r) = (e_1, dots, e_r) P_rho, quad rho in G.
  $
  Let us put $bold(e) = (e_1, dots, e_r)$. Then the preceding formulas may be
  written briefly as
  $
    x bold(e) = bold(e) T(x), quad rho bold(e) = bold(e) P_rho, quad x in E,
    quad rho in G.
  $ <eq:matrices-of-field-and-group>
  The isomorphism $(E slash L, 1) tilde.equiv M_r (L)$, given by
  @cor:crossed-product-trivial-factor-set, is obtained by the mapping
  $x -> T(x)$, $rho -> P_rho$, $x in E$, $rho in H$. Let
  $
    T(E) = {T(x) : x in E},
  $
  a field $L$-isomorphic to $E$. Then we have
  $
    M_r (L) = dsum_(rho in H) T(E) P_rho.
  $ <eq:matrix-algebra-crossed-product>

  For each matrix $X$ with entries in $L$, and each $sigma in G$, let $sigma(X)$
  be the matrix obtained from $X$ by applying $sigma$ to each of its entries.
  Then
  $
    (rho sigma) bold(e) = rho(bold(e) P_sigma) = bold(e) P_rho dot
    rho(P_sigma), quad rho, sigma in G,
  $
  whence
  $
    P_(rho sigma) = P_rho dot rho(P_sigma), quad rho, sigma in G.
  $ <eq:matrix-cocycle>
  On the other hand, for $x in E$ and $sigma in G$ we obtain
  $
    sigma(x) sigma(bold(e)) & = sigma(x bold(e)) = sigma(bold(e) T(x)) \
                            & = sigma bold(e) dot sigma(T(x)) = bold(e) P_sigma
                              dot sigma(T(x)).
  $
  But also
  $
    sigma(x) sigma(bold(e)) = sigma(x) dot bold(e) P_sigma = bold(e)
    T(sigma(x)) P_sigma.
  $
  Therefore
  $
    T(sigma(x)) dot P_sigma = P_sigma dot sigma(T(x)), quad x in E, quad
    sigma in G.
  $ <eq:matrix-conjugation>

  We are now ready to return to the $K$-algebra $B$ defined above. We may write
  $
    B = (L slash K, f) times.o_K M_r (K) = dsum_(overline(sigma) in
    overline(G)) L u_(overline(sigma)) times.o M_r (K) tilde.equiv
    dsum_(overline(sigma) in overline(G)) M_r (L) u_(overline(sigma)).
  $
  #source(260)In the above, the symbols ${u_(overline(sigma))}$ multiply
  according to the normalized factor set $f$, and in the last summation we have
  written $u_(overline(sigma))$ in place of $u_(overline(sigma)) times.o 1$.
  From the definition of the crossed-product algebra $(L slash K, f)$, we have
  $
    u_(overline(sigma)) dot y = overline(sigma)(y) dot u_(overline(sigma)),
    quad y in L, quad overline(sigma) in overline(G).
  $
  Therefore
  $
    u_(overline(sigma)) dot X = overline(sigma)(X) dot u_(overline(sigma)),
    quad X in M_r (L), quad overline(sigma) in overline(G).
  $
  Let us identify $B$ with $dsum M_r (L) u_(overline(sigma))$, and let us use
  formula @eq:matrix-algebra-crossed-product for $M_r (L)$. Then we may write
  $
    B = dsum_(rho in H, overline(sigma) in overline(G)) T(E) P_rho
    u_(overline(sigma)).
  $
  We have now exhibited an embedding of $E$ in $B$, since $E tilde.equiv T(E)$.
  Of course $P_1$ is the identity matrix in $M_r (L)$, and $u_(overline(1))$ is
  the unity element of $B$. We are trying to prove that
  $B tilde.equiv (E slash K, g)$.

  Let us write $G = H sigma_1 union dots.c union H sigma_s$. Each $sigma in G$
  is uniquely expressible as $sigma = rho sigma_i$, for some $rho in H$ and some
  $i$ between 1 and $s$. Then $overline(sigma) = overline(sigma)_i$, and of
  course $overline(G) = {overline(sigma)_1, dots, overline(sigma)_s}$. Now
  define
  $
    v_sigma = P_sigma u_(overline(sigma)) in B, quad sigma in G.
  $
  We shall show that
  $
    B = dsum_(sigma in G) T(E) v_sigma.
  $ <eq:inflation-basis>
  Let $sigma = rho sigma_i$, $rho in H$, $1 <= i <= s$. By @eq:matrix-cocycle,
  $P_sigma = P_rho dot rho(P_(sigma_i))$. Since $P_(sigma_i)$ has entries in
  $L$, and since $rho in H$, it follows that $P_sigma = P_rho dot P_(sigma_i)$.
  Furthermore, $P_(sigma_i)$ is a unit in the ring $dsum_(rho in H) T(E) P_rho$.
  Therefore
  $
    B & = dsum_(i=1)^s {dsum_(rho in H) T(E) P_rho} u_(overline(sigma)_i) =
        dsum_i {dsum_rho T(E) P_rho} P_(sigma_i) u_(overline(sigma)_i) \
      & = dsum_(i, rho) T(E) P_(rho sigma_i) u_(overline(sigma)_i) =
        dsum_(sigma in G) T(E) v_sigma,
  $
  which establishes formula @eq:inflation-basis.

  We are going to prove that $B tilde.equiv (T(E) slash K, g)$, and so shall
  first compute $tilde(G) = Gal(T(E) slash K)$. Since $E tilde.equiv T(E)$, it
  follows that $tilde(G) = {tilde(sigma) : sigma in G}$, where
  $
    tilde(sigma)(T(x)) = T(sigma x), quad x in E, quad sigma in G.
  $
  Using this formula, we may now compute the action of $v_sigma$ on $T(x)$, for
  $sigma in G$ and $x in E$. We have
  $
    v_sigma dot T(x) = P_sigma u_(overline(sigma)) dot T(x) = P_sigma dot
    overline(sigma)(T(x)) dot u_(overline(sigma)).
  $
  But $overline(sigma)(Y) = sigma(Y)$ for any $Y in M_r (L)$ and any
  $sigma in G$, since $sigma$ acts as $overline(sigma)$ on elements #source(
    261,
  )of $L$. Hence by @eq:matrix-conjugation we obtain
  $
    v_sigma dot T(x) & = P_sigma dot sigma(T(x)) dot u_(overline(sigma)) =
                       T(sigma(x)) dot P_sigma dot u_(overline(sigma)) \
                     & = T(sigma(x)) dot v_sigma = tilde(sigma)(T(x)) dot
                       v_sigma, quad x in E, quad sigma in G.
  $
  This proves that $v_sigma$ transforms $T(E)$ according to the action of
  $tilde(sigma)$ on $T(E)$.

  Finally, we obtain
  $
    v_sigma v_tau & = P_sigma u_(overline(sigma)) dot P_tau u_(overline(tau)) =
                    P_sigma dot overline(sigma)(P_tau) dot u_(overline(sigma))
                    dot u_(overline(tau)) \
                  & = P_sigma dot sigma(P_tau) dot f_(overline(sigma),
                    overline(tau)) u_(overline(sigma) overline(tau)) =
                    P_(sigma tau) f_(overline(sigma), overline(tau))
                    u_(overline(sigma) overline(tau)) \
                  & = g_(sigma, tau) v_(sigma tau), quad sigma, tau in G.
  $
  This establishes that $B tilde.equiv (T(E) slash K, g)$ as claimed, and
  completes the proof of the theorem.
]

#remark(kind: "Remarks", numbered: false)[
  + Let $L slash K$ be a finite galois extension, $F$ an intermediate field, and
    set
    $
      G = Gal(L slash K), quad H = Gal(L slash F).
    $
    Since $H$ is a subgroup of $G$, each factor set from $G$ to $L^*$ restricts
    to a factor set from $H$ to $L^*$, thereby inducing a homomorphism
    $
      res: H^2 (G, L^*) -> H^2 (H, L^*).
    $
    On the other hand, by @th:brauer-group-extension-map there is a homomorphism
    $
      F times.o_K dot : B(L slash K) -> B(L slash F).
    $
    Formula @eq:crossed-product-restriction is equivalent to the assertion that
    the following diagram commutes:
    $
      #ladder(
        ($H^2 (G, L^*)$, $H^2 (H, L^*)$),
        ($B(L slash K)$, $B(L slash F) ,$),
        ([], []),
        top-maps: ($res$,),
        bottom-maps: ($F times.o_K dot$,),
        gap: 12mm,
        row: 10mm,
      )
    $
    where the vertical arrows denote the isomorphisms given by
    @th:crossed-products-brauer-group.
  + Keeping the above notation, assume further that $H normal G$, and set
    $overline(G) = G slash H = Gal(F slash K)$. As in the proof of
    @th:crossed-product-inflation, each factor set from $overline(G)$ to $F^*$
    inflates to a factor set from $G$ to $L^*$, thereby inducing a homomorphism
    $
      inf: H^2 (overline(G), F^*) -> H^2 (G, L^*).
    $
    On the other hand, each central simple $K$-algebra split by $F$ is also
    split by $L$, so there is a monomorphism $B(F slash K) -> B(L slash K)$.
    @th:crossed-product-inflation[Theorem] is equivalent to the assertion that
    the following diagram commutes:
    #source(262)
    $
      #ladder(
        ($H^2 (overline(G), F^*)$, $H^2 (G, L^*)$),
        ($B(F slash K)$, $B(L slash K) ,$),
        ([], []),
        top-maps: ($inf$,),
        gap: 12mm,
        row: 10mm,
      )
    $
    where the vertical arrows are the isomorphisms of
    @th:crossed-products-brauer-group.
]

We conclude this section with a discussion of the relation between the exponent
and the index of an element of the Brauer group $B(K)$. For $[A] in B(K)$, let
$exp [A]$ denote the _exponent_#idx("$exp [A]$") of $[A]$ in $B(K)$, that is,
the least positive integer $t$ such that $[A]^t = 1$ in $B(K)$. On the other
hand, define the _index_#idx("index $[A]$") of $[A]$ to be the index of the
skewfield part of $A$. This means that for $[A] in B(K)$,
$
  index [A] = index [D] = sqrt((D : K)),
$
where $D$ is a skewfield such that $A tilde.op D$.

#theorem(major: true)[
  For each $[A] in B(K)$, we have
  $
    [A]^m = 1 "in" B(K), quad "where" quad m = index [A].
  $
  Therefore $exp [A]$ divides $index [A]$.
] <th:exponent-divides-index>

#proof[
  Let $A tilde.op D$, where $D$ is a skewfield of index $m$, so $[A] = [D]$ in
  $B(K)$. By @cor:galois-splitting-field there exists a finite galois extension
  $L$ of $K$ such that $L$ splits $A$. Then $L$ also splits $D$. As in the proof
  of @th:splitting-field-matrix-embedding, using $L$ in place of the field $E$
  occurring in that proof, we let $V$ be a simple right
  $(L times.o_K D)$-module, and set $r = (V : D)$. Then there is an embedding
  $
    L subset Hom_D (V, V) = B, quad B tilde.equiv M_r (D),
  $
  and $(L : K) = m r$ by @eq:splitting-field-dimension. On the other hand, we
  may view $V$ as left $B$-module, and then $B tilde.equiv V^((r))$ as left
  $B$-modules. Therefore
  $
    r(V : L) = (B : L) = (B : K) slash (L : K) = m r,
  $
  and so $(V : L) = m$.

  Since $L$ is a self-centralizing maximal subfield of the central simple
  $K$-algebra $B$, it follows as in @th:crossed-products-brauer-group that there
  exists a factor set $f: G times G -> L^*$ such that
  $B tilde.equiv (L slash K, f)$. Hence by @th:crossed-product-tensor we obtain
  $
    [A]^m = [B]^m = [(L slash K, f^m)] quad "in" quad B(K).
  $
  It therefore suffices to prove that $f^m$ is a principal factor set. This will
  be done by using a technique of Schur, who first proved this theorem. Each
  $sigma in G = Gal(L slash K)$ determines an element
  $u_sigma in (L slash K, f)$. We shall identify $B$ with $(L slash K, f)$, and
  then the element $u_sigma$ of $B$ acts on the left $B$-module $V$. If #source(
    263,
  )$P^((sigma))$ describes the action of $u_sigma$ on some specific $L$-basis of
  $V$, then we have obtained a mapping
  $
    sigma in G -> P^((sigma)) in M_m (L).
  $
  We shall show that this mapping satisfies the identity
  $
    f_(sigma, tau) P^((sigma tau)) = P^((sigma)) dot sigma{P^((tau))}, quad
    sigma, tau in G,
  $ <eq:schur-matrices>
  where $sigma{P^((tau))}$ is obtained from $P^((tau))$ by applying $sigma$ to
  each of its entries.

  To establish the above formula, let us recall that $(V : L) = m$, so we may
  write $V = dsum_(i=1)^m L v_i$. For $sigma in G$, let us set
  $
    u_sigma dot v_j = sum_i p_(i j)^((sigma)) v_i, quad P^((sigma)) =
    (p_(i j)^((sigma))) in M_m (L).
  $
  Then
  $
    (u_sigma u_tau) v_j = u_sigma {sum_k p_(k j)^((tau)) v_k} = sum_(i, k)
    sigma(p_(k j)^((tau))) dot p_(i k)^((sigma)) v_i.
  $
  On the other hand,
  $
    (u_sigma u_tau) v_j = (f_(sigma, tau) u_(sigma tau)) v_j = f_(sigma, tau)
    dot sum_i p_(i j)^((sigma tau)) v_i.
  $
  Comparing this formula with the preceding one, we deduce @eq:schur-matrices at
  once.

  Now take determinants in @eq:schur-matrices, and let
  $c_sigma = det P^((sigma)) in L^*$. Then we obtain
  $
    (f_(sigma, tau))^m dot c_(sigma tau) = c_sigma dot sigma(c_tau), quad
    sigma, tau in G.
  $
  Therefore $f^m = delta c$, a principal factor set, and so
  $[A]^m = [B]^m = [(L slash K, f^m)] = 1$ in $B(K)$. This completes the proof.
]

As we shall see in Chapter~@ch:simple-algebras-over-global-fields (see
@th:index-equals-exponent),
$
  exp [A] = index [A], quad [A] in B(K),
$
when $K$ is any algebraic number field. For the moment, we content ourselves
with a somewhat weaker result, which holds for general $K$.

#theorem[
  For each $[A] in B(K)$, the integers $exp [A]$ and $index [A]$ have the same
  prime factors, apart from multiplicities.
] <th:exponent-index-same-primes>

#proof[
  We may assume that $A$ is a skewfield $D$ with center $K$ and index $m$. Since
  $exp [D]$ divides $m$ by @th:exponent-divides-index, it suffices for us to
  prove that each rational prime $p$ dividing $m$ also divides $exp [D]$. We
  shall suppose that $p | m$, $p divides.not exp [D]$, and shall obtain a
  contradiction.

  There exists a finite galois extension $L slash K$ such that $L$ splits $D$,
  by @cor:galois-splitting-field. Let $G = Gal(L slash K)$, and let $H$ be a
  Sylow $p$-subgroup of $G$. Then
  #source(264)
  $
    abs(H) = p^r, r >= 0, quad [G : H] = q, quad p divides.not q.
  $
  Let $E$ be the subfield of $L$ fixed by $H$; then $(E : K) = [G : H] = q$.
  Since $m divides.not q$, it follows from
  @th:splitting-field-matrix-embedding[(i)] that $E$ does _not_ split $D$. Then
  $S = E times.o_K D$ is a central simple $E$-algebra, such that $[S] != 1$ in
  $B(E)$. Consider the diagram
  $
    #sylow-fields
  $
  The homomorphism $B(K) -> B(E)$ defined by $E times.o_K dot$, carries $[D]$
  onto $[S]$. Therefore $exp [S]$ divides $exp [D]$. Since
  $p divides.not exp [D]$, we conclude that $p divides.not exp [S]$. On the
  other hand, we have
  $
    L times.o_E S = L times.o_E (E times.o_K D) tilde.equiv L times.o_K D
    tilde.equiv M_m (L),
  $
  since $L$ splits $D$. Therefore $L$ also splits $S$, and so $n | (L : E)$ by
  @th:splitting-field-matrix-embedding[(i)], where $n$ is the index of $S$.
  Hence $n$ is a power of $p$. However, by @th:exponent-divides-index we know
  that $exp [S]$ divides $n$, so $exp [S]$ is also a power of $p$. But we have
  shown above that $p divides.not exp [S]$, and so it follows that $[S] = 1$ in
  $B(E)$. This is a contradiction, and thus the theorem must be true.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Show that every factor set $f: G times G -> L^*$ is equivalent to a normalized
  factor set. #hint[@exc:normalized-factor-set][Let $c_1 = f_(1, 1)^(-1)$,
    $c_sigma = 1$ for $sigma in G - {1}$. Then
    $(delta c)_(sigma, 1) = sigma(c_1)$, $sigma in G$. Set $g = (delta c) f$,
    and show first that $g_(1, 1) = 1$, then that $g_(sigma, 1) = g_(1, sigma) =
    1$ for all $sigma in G$.] <hint:normalized-factor-set>
] <exc:normalized-factor-set>

#exercise[
  Verify that $(L slash K, f)$ has center $K$, and that $L$ is its own
  centralizer in $(L slash K, f)$.
] <exc:crossed-product-center>

#exercise[
  Let $e$ be an idempotent of the central simple $K$-algebra $C$. Prove that
  $C tilde.op e C e$. #hint[@exc:idempotent-corner-similar][We may take
    $C = M_r (D)$, $D =$ skewfield with center $K$. After a suitable change of
    basis (see Exercise~@exc:conjugate-idempotents), we may assume that
    $e = diag(1, dots, 1, 0, dots, 0)$, where $s$ 1’s occur. But then
    $e C e tilde.equiv M_s (D) tilde.op D tilde.op C$.]
  <hint:idempotent-corner-similar>
] <exc:idempotent-corner-similar>

#exercise[
  Let $D$ be a skewfield with center $K$, index $m$. Let $E$ be a finite field
  extension of $K$, and let $E times.o_K D tilde.equiv M_r (S)$, where $S$ is a
  skewfield of index $n$. Show that $S$ has center $E$, and that $m slash n$ is
  an integer which divides $(E : K)$. #hint[@exc:index-reduction][This is the
    _Index Reduction Theorem_#idx("Index Reduction Theorem") of Albert
    [@bib:Albert1939]. To prove it, note first that $E times.o_K D$ is a central
    simple $E$-algebra, so $S$ has center $E$. Next,
    $
      m^2 = (E times.o_K D : E) = (M_r (S) : E) = r^2 n^2,
    $
    so $r = m slash n$. Finally, if $V$ is a simple right $M_r (S)$-module, then
    $M_r (S) tilde.equiv V^((r))$. Comparing #source(265)right $D$-dimensions,
    we obtain
    $
      (E : K) = r(V : D),
    $
    so $r | (E : K)$.] <hint:index-reduction>
] <exc:index-reduction>

#exercise[
  Keep the notation of the preceding exercise. Prove that if $(E : K)$ is
  relatively prime to the index $m$ of $D$, then $E times.o_K D$ is a skewfield
  with center $E$ and index $m$. #hint[@exc:coprime-extension-skewfield][Using
    the notation of Exercise~@exc:index-reduction, we see that $r = 1$, since
    $r$ divides both $m$ and $(E : K)$.] <hint:coprime-extension-skewfield>
] <exc:coprime-extension-skewfield>

#exercise[
  Let $D_i$ be a skewfield with center $K$, index $m_i$, $i = 1, 2$, and suppose
  that $(m_1, m_2) = 1$. Prove that $D_1 times.o_K D_2$ is a skewfield with
  center $K$ and index $m_1 m_2$. #hint[@exc:coprime-tensor-skewfield][Let
    $D_1 times.o_K D_2 tilde.equiv M_t (S)$, where $S$ is a skewfield with
    center $K$, and let $E$ be a maximal subfield of $S$. Then $E$ splits $S$,
    so
    $
      [E times.o_K D_1][E times.o_K D_2] = 1 "in" B(E).
    $
    But under the homomorphism $B(K) -> B(E)$, $[D_i]$ maps onto
    $[E times.o_K D_i]$. Since $[D_i]^(m_i) = 1$, this shows that
    $[E times.o_K D_1]$ and $[E times.o_K D_2]$ have relatively prime orders.
    Therefore $[E times.o_K D_i] = 1$ in $B(E)$, $i = 1, 2$, so $E$ splits both
    $D_1$ and $D_2$. Then $(E : K)$ is divisible by $m_1$ and $m_2$, so
    $(E : K) >= m_1 m_2$. Therefore
    $
      (S : K) = (E : K)^2 >= m_1^2 m_2^2 & = (D_1 : K)(D_2 : K) \
                                         & = (D_1 times.o_K D_2 : K) =
                                           (M_t (S) : K),
    $
    so $S = M_t (S)$. This proves that $t = 1$, and that
    $(S : K) = m_1^2 m_2^2$.] <hint:coprime-tensor-skewfield>
] <exc:coprime-tensor-skewfield>

#exercise[
  Let $D$ be a skewfield with center $K$ and index $m$, where
  $m = product_(i=1)^t p_i^(e_i)$, with the ${p_i}$ distinct primes and each
  $e_i >= 1$. Prove that there exist skewfields $D_1, dots, D_t$ with center
  $K$, such that $D_i$ has index $p_i^(e_i)$, and
  $
    D tilde.equiv D_1 times.o_K dots.c times.o_K D_t.
  $ <eq:skewfield-primary-decomposition>
  #hint[@exc:skewfield-primary-decomposition][$exp [D]$ divides $m$, and each
    $p_i | exp [D]$. We may then write
    $
      [D] = [A_1] dots.c [A_t] quad "in" quad B(K),
    $
    where $exp [A_i] = p_i^(b_i)$, with $1 <= b_i <= e_i$. Let $D_i$ be the
    skewfield part of $A_i$. Then
    $
      [D] = [D_1] dots.c [D_t] = [D_1 times.o_K dots.c times.o_K D_t] quad
      "in" quad B(K).
    $
    But $index [D_i] = p_i^(c_i)$ for some $c_i >= 1$, by
    @th:exponent-index-same-primes. Hence $D_1 times.o_K dots.c times.o_K D_t$
    is a skewfield, by Exercise~@exc:coprime-tensor-skewfield, and so
    @eq:skewfield-primary-decomposition is valid.]
  <hint:skewfield-primary-decomposition>
] <exc:skewfield-primary-decomposition>

No hints will be given for
Exercises~@exc:standard-resolution–@exc:cyclic-galois-cohomology. The reader may
consult the references on cohomology of groups listed at the start of this
chapter.

#exercise[
  Let $G$ be a finite group, and let $bold(Z) G$ be the _integral group
  ring_#idx("integral group ring")#idx("group ring") consisting of all sums
  ${sum_(g in G) alpha_g g : alpha_g in bold(Z)}$ (see beginning of
  §~@sec:orders-definitions-and-examples, example (iv)). Every additive group
  $M$, on which $G$ acts as left operator domain, can be made into a left
  $bold(Z) G$-module. Let $bold(Z)$ be the _trivial_ $bold(Z) G$-module#idx(
    "trivial $bold(Z) G$-module",
  ), that is, the additive group $bold(Z)$ on which $G$ acts trivially:
  $g z = z$, $g in G$, $z in bold(Z)$. Let $Q_n$ be the free left
  $bold(Z) G$-module having as free basis the collection of all $n$-tuples
  $[x_1, dots, x_n]$ of elements of $G$. For $n = 0$, interpret $Q_0$ as the
  free module on #source(266)one generator, with this generator denoted by the
  empty bracket $[thick]$. Show that there is a $bold(Z) G$-exact sequence
  $
    -> Q_2 stretch(->)^(d_2) Q_1 stretch(->)^(d_1) Q_0 stretch(->)^(d_0)
    bold(Z) -> 0,
  $ <eq:standard-resolution>
  where
  $
    & d_0 [thick] = 1, \
    & d_1 [x] = x[thick] - [thick], \
    & d_2 [x, y] = x[y] - [x y] + [x], \
    & d_3 [x, y, z] = x[y, z] - [x y, z] + [x, y z] - [x, y], quad x, y, z in G,
  $
  and so on. Each map $d_i$ is a left $bold(Z) G$-homomorphism, that is,
  $
    d_i {xi[x_1, dots, x_i]} = xi d_i [x_1, dots, x_i], quad xi in bold(Z) G,
    quad x_nu in G.
  $
] <exc:standard-resolution>

#exercise[
  Given a left $bold(Z) G$-module $M$, we apply $Hom_(bold(Z) G) (dot, M)$ to
  @eq:standard-resolution, obtaining a sequence of additive groups
  $
    0 -> Hom_(bold(Z) G) (bold(Z), M) stretch(->)^(d_0^*) Hom_(bold(Z) G)
    (Q_0, M) stretch(->)^(d_1^*) Hom_(bold(Z) G) (Q_1, M)
    stretch(->)^(d_2^*) dots.c,
  $ <eq:cochain-sequence>
  where $d_i$ induces $d_i^*$ as in §~@ss:modules. Thus
  $
    d_i^* f = f d_i, quad f in Hom_(bold(Z) G) (Q_(i-1), M), quad
    Q_(-1) = bold(Z).
  $
  Prove first that $im d_i^* subset ker d_(i+1)^*$. Then define
  $
    H^0 (G, M) = ker d_1^*, quad H^n (G, M) = ker d_(n+1)^* slash im d_n^*,
    quad n >= 1.
  $
  Call $H^n (G, M)$ the $n$th _cohomology group_#idx("cohomology group") of $G$
  with coefficients in $M$. Prove that
  $
    H^n (G, M) tilde.equiv Ext_(bold(Z) G)^n (bold(Z), M), quad n >= 0,
  $ <eq:cohomology-ext>
  where on the right, $bold(Z)$ denotes the trivial $bold(Z) G$-module.
] <exc:cohomology-groups>

#exercise[
  Keep the above notation. Each $f in Hom_(bold(Z) G) (Q_n, M)$ is determined by
  its values ${f[x_1, dots, x_n]}$ in $M$, so we may identify
  $Hom_(bold(Z) G) (Q_n, M)$ with the additive group of all maps
  $
    f: underbrace(G times dots.c times G, n "factors") -> M.
  $
  For $n = 0$, identify $Hom_(bold(Z) G) (Q_0, M)$ with $M$, letting
  $f in Hom_(bold(Z) G) (Q_0, M)$ correspond to $f[thick] in M$. Prove that
  $
    & (d_1^* f)[x] = f(d_1 [x]) = x f[thick] - f[thick], quad "where"
      f: [thick] -> M, \
    & (d_2^* f)[x, y] = x f(y) - f(x y) + f(x), quad "where" f: G -> M, \
    & (d_3^* f)[x, y, z] = x f(y, z) - f(x y, z) + f(x, y z) - f(x, y), \
    & quad quad "where" f: G times G -> M,
  $
  and so on. Prove that $H^0 (G, M) tilde.equiv M^G$ as additive groups, where
  $
    M^G = {m in M : g m = m quad "for all" g in G}.
  $
] <exc:cochains>

#exercise[
  #source(267)Keep the above notation, and let $G = Gal(L slash K)$, where
  $L slash K$ is a finite galois extension. Choose $M$ to be the multiplicative
  group $L^*$ on which $G$ acts, and view $M$ as $bold(Z) G$-module. Show that
  $ker d_3^*$ consists of all factor sets from $G$ to $L^*$, and that $im d_2^*$
  consists of all principal factor sets. Deduce that the second cohomology group
  $H^2 (G, L^*)$, defined at the beginning of §~@sec:crossed-product-algebras,
  is a special case of the cohomology groups given in
  Exercise~@exc:cohomology-groups.
] <exc:factor-sets-cocycles>

#exercise[
  Let $G = chevron.l sigma chevron.r$ be a finite cyclic group of order $n$, and
  let $M$ be a left $bold(Z) G$-module. Let
  $
    D = sigma - 1, quad N = 1 + sigma + sigma^2 + dots.c + sigma^(n-1) in
    bold(Z) G.
  $
  Prove that there is a $bold(Z) G$-exact sequence
  $
    dots.c stretch(->)^N bold(Z) G stretch(->)^D bold(Z) G stretch(->)^N
    bold(Z) G stretch(->)^D bold(Z) G stretch(->)^epsilon bold(Z) -> 0,
  $
  where $stretch(->)^N$ means left multiplication by $N$, $stretch(->)^D$ by
  $D$, and where $epsilon$ is the _augmentation map_#idx("augmentation map")
  defined by
  $
    epsilon(sum_(g in G) alpha_g g) = sum_(g in G) alpha_g, quad alpha_g in
    bold(Z).
  $
  Using this projective resolution of the trivial $bold(Z) G$-module $bold(Z)$,
  deduce that $H^0 (G, M) tilde.equiv M^G$, and that
  $
    cases(
      H^1 (G, M) tilde.equiv H^3 (G, M) tilde.equiv H^5 (G, M) tilde.equiv
      dots.c tilde.equiv M' / ((sigma - 1) M)",",
      H^2 (G, M) tilde.equiv H^4 (G, M) tilde.equiv H^6 (G, M) tilde.equiv
      dots.c tilde.equiv M^G / ((1 + sigma + dots.c + sigma^(n-1)) M).
    )
  $ <eq:cyclic-cohomology>
  Here,
  $
    M' = {m in M : N m = 0} = {m in M : (1 + sigma + dots.c + sigma^(n-1)) m =
      0}.
  $
] <exc:cyclic-group-cohomology>

#exercise[
  Let $L slash K$ be a finite galois extension, with galois group
  $G = chevron.l sigma chevron.r$ cyclic of degree $n$. Choosing $M = L^*$ in
  the preceding exercise, show that
  $
    M^G = {x in L^* : sigma x = x} = K^*, quad (1 + sigma + dots.c +
      sigma^(n-1)) M = N_(L slash K) (L^*),
  $
  where $N_(L slash K) (L^*) = {N_(L slash K) x : x in L^*}$. Deduce that
  $
    H^2 (G, L^*) tilde.equiv K^* slash N_(L slash K) (L^*).
  $ <eq:cyclic-galois-h2>
] <exc:cyclic-galois-cohomology>

#exercise[
  Let $L slash K$ be a finite galois extension, with galois group $G$. Prove the
  _Normal Basis Theorem_: #idx("normal basis theorem")

  _There exists an $x in L$ such that ${sigma(x) : sigma in G}$ is a $K$-basis
  of $L$._

  #hint(title: [Berger–Reiner [@bib:Berger1975]])[@exc:normal-basis-theorem][Let
    $A = (L slash K, 1) tilde.equiv Hom_K (L, L)$, as in the proof of
    @cor:crossed-product-trivial-factor-set, so $L$ is a left module over the
    simple ring $A$. Comparing $K$-dimensions, it follows that
    $A tilde.equiv L^((n))$ as left $A$-modules. Let
    $
      A = dsum_(sigma in G) L u_sigma, quad B = dsum_(sigma in G) K u_sigma,
      quad u_sigma u_tau = u_(sigma tau), quad sigma, tau in G,
    $
    where $u_sigma dot x = sigma(x) u_sigma$, $sigma in G$, $x in L$. #source(
      268,
    )Then $B$ is a subring of $A$. If $L = dsum_(i=1)^n K x_i$, then
    $
      A = dsum_sigma u_sigma L = dsum_i {dsum_sigma K u_sigma} x_i tilde.equiv
      B^((n))
    $
    as left $B$-modules.

    Hence $L^((n)) tilde.equiv B^((n))$ as left $B$-modules, whence
    $L tilde.equiv B$ by the Krull–Schmidt Theorem
    (Exercise~@exc:krull-schmidt). Therefore $L = B x$ for some $x in L$, and
    $
      B x = (sum_(sigma in G) K u_sigma) x = sum_(sigma in G) K sigma(x).
    $] <hint:normal-basis-theorem>
] <exc:normal-basis-theorem>
