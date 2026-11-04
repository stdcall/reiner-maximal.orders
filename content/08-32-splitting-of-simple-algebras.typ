#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/08-32-splitting-of-simple-algebras.typ": subgroup-tower

== Splitting of simple algebras <sec:splitting-of-simple-algebras>

Let $A$ be a central simple $K$-algebra, where $K$ is a global field, and let
$P$ range over the primes of $K$ (see §~@ss:global-fields). In order to simplify
the notation, we shall use $K_P$ (rather than $hat(K)_P$) to denote the $P$-adic
completion of $K$. Then put
$
  A_P = K_P times.o_K A = P"-adic completion of" A.
$
By @cor:central-simple-extension, $A_P$ is a central simple $K_P$-algebra; thus
the map $[A] -> [A_P]$ yields a homomorphism of Brauer groups $B(K) -> B(K_P)$.
Suppose that
$
  A_P tilde.equiv M_(kappa_P) (S),
$
where $S$ is a skewfield of index $m_P$ over its center $K_P$. As in
§§~@sec:different-discriminant-global, @sec:crossed-product-algebras, we call
$m_P$ the _local index_ of $A$ at $P$, and we write
$
  m_P = index [A_P].
$
We call $kappa_P$ the _local capacity_ of $A$ at $P$. Clearly
$
  A_P tilde.op K_P quad "if and only if" quad m_P = 1.
$
We shall say that $A$ _ramifies_ at $P$, or that $P$ is _ramified_ in $A$, if
$m_P > 1$. #idx("ramification (at $P$)")#idx("ramified prime")

The following theorem summarizes some of the main results of
Chapter~@ch:maximal-orders-over-dedekind-domains (see
@th:prime-ideals-of-maximal-order, @th:different-global-field and
@cor:ground-ideal-discriminant).

#theorem[
  #source(282)Let $R$ be a Dedekind domain whose quotient field is a global
  field $K$, and assume that $R != K$. Let $Lambda$ be a maximal $R$-order in
  the central simple $K$-algebra $A$. The nonzero prime ideals $P$ of $R$, and
  the prime ideals $frak(P)$ of $Lambda$, are in one-to-one correspondence,
  given by
  $
    P = R inter frak(P), quad frak(P) | P Lambda.
  $
  Let $m_P$ be the local index of $A$ at $P$ and $kappa_P$ the local capacity of
  $A$ at $P$. Then
  + $m_P = 1$ a.e., that is, $A_P tilde.op K_P$ a.e.
  + $P Lambda = frak(P)^(m_P)$ for all $P$.
  + Let $frak(D)(Lambda slash R)$ denote the different of $Lambda$ with respect
    to $R$, and $d(Lambda slash R)$ the discriminant. Then
    $
      frak(D)(Lambda slash R) = product_P frak(P)^(m_P - 1), quad
      d(Lambda slash R) = {product_P P^((m_P - 1) kappa_P)}^(sqrt((A : K))).
    $
  + We have
    $
      m_P > 1 <==> P | d(Lambda slash R) <==> frak(P) | frak(D)(Lambda slash R)
      <==> frak(P)^2 | P Lambda.
    $
] <th:maximal-order-local-indices>

In the present discussion, the infinite primes of $K$ will play an important
role. Such infinite primes occur only when $K$ is an algebraic number field. In
this case, an infinite prime $P$ of $K$ corresponds to an archimedean valuation
on $K$ which extends the ordinary absolute value on the rational field
$bold(Q)$. The $P$-adic completion $K_P$ is either the real field $bold(R)$ (in
which case $P$ is called a _real prime_), or else the complex field $bold(C)$
(and $P$ is a _complex prime_).

#theorem[
  Let $A$ be a central simple $K$-algebra, and let $m_P$ be the local index of
  $A$ at an infinite prime $P$ of $K$.
  + If $P$ is a complex prime, then
    $
      A_P tilde.op K_P quad "and" quad m_P = 1.
    $
  + If $P$ is a real prime, then either
    $
      A_P tilde.op K_P quad "and" quad m_P = 1,
    $
    or else
    $
      A_P tilde.op bold(H) quad "and" quad m_P = 2,
    $
    where $bold(H)$ is the skewfield of real quaternions (see
    Exercise~@exc:real-quaternions-cyclic).
] <th:infinite-prime-local-index>

#proof[
  Clearly $A_P tilde.op D$, where $D$ is a skewfield with center $K_P$, and
  $(D : K_P)$ is finite. If $P$ is complex, then $D = bold(C) = K_P$ by
  Exercise~@exc:skewfield-over-algebraically-closed. If $P$ is real, then
  $K_P = bold(R)$, and $D = bold(R)$ or $bold(H)$ by
  Exercise~@exc:real-skewfields. This completes the proof.
]

If $P$ is any finite prime of $K$, then $K_P$ is a complete field relative to a
discrete valuation, and has a finite residue class field. We saw in
§~@sec:cyclic-algebras-local how to define the #source(283)Hasse invariant
$inv [A_P]$ of a central simple $K_P$-algebra, thereby obtaining an isomorphism
$inv: B(K_P) tilde.equiv bold(Q) slash bold(Z)$. We showed in fact (see
@th:exponent-equals-index and @eq:hasse-invariant) that
$
  cases(
    inv [A_P] = s_P slash m_P,
    exp [A_P] = m_P,
  ) "," quad "where" m_P = index [A_P], quad (s_P, m_P) = 1.
$ <eq:local-invariant-exponent>

We would like to have the same formulas true for the case of infinite primes.
First we must define Hasse invariants when $P$ is an infinite prime, and in
light of @th:infinite-prime-local-index, it is sufficient to define these
invariants for the three cases $bold(C)$, $bold(R)$ and $bold(H)$. We set #idx(
  "Hasse invariant",
)#idx("invariant (Hasse)")
$
  inv [bold(C)] = 0, quad inv [bold(R)] = 0, quad
  inv [bold(H)] = 1/2.
$ <eq:infinite-hasse-invariants>
Formulas @eq:local-invariant-exponent then hold equally well when $P$ is
infinite, provided we know that $exp [bold(H)] = 2$ when $[bold(H)]$ is
considered as an element of $B(bold(R))$. We have already observed this fact in
Exercise~@exc:quaternions-exponent-two.

Now let $A$ be any central simple $K$-algebra, and let $P$ be any prime of $K$
(finite or infinite). Clearly,
$
  A tilde.op K => A_P tilde.op K_P "for all" P.
$
We shall prove the extremely important converse of this implication, by using
the Hasse Norm Theorem (see below). First of all, we must review some facts from
galois theory. Some of these results have already been mentioned in
§~@sec:dedekind-domains and §~@ss:extensions-of-valuations. Proofs are readily
available in the references listed at the beginning of §~@sec:dedekind-domains.

Let $L$ be a finite galois extension of $K$, with galois group
$G = Gal(L slash K)$. Let $P$ be a prime of $K$, finite or infinite. Even when
$P$ is a finite prime, it will be convenient to think of $P$ as representing a
class of valuations on $K$, rather than an ideal in some valuation ring. From
this point of view, the valuation $P$ extends to a finite set of inequivalent
valuations on $L$, denoted by $frak(p)$ ($= frak(p)_1$),
$frak(p)_2, dots, frak(p)_g$. For each $sigma in G$, there is a valuation
$frak(p)^sigma$ on $L$, defined by the formula
$
  frak(p)^sigma lr((x)) = frak(p)(sigma^(-1) x), quad x in L.
$
We call $frak(p)^sigma$ a _conjugate_ of $frak(p)$; if $frak(p)$ is a finite
prime, then $sigma$ carries the valuation ring of $frak(p)$ onto the valuation
ring of $frak(p)^sigma$. Whether or not $frak(p)$ is finite, each $frak(p)_i$ is
of the form $frak(p)^sigma$ for some $sigma in G$.

Keeping the above notation, we set
$
  G_frak(p) = {sigma in G : frak(p)^sigma = frak(p)},
$ <eq:decomposition-group>
and call $G_frak(p)$ the _decomposition group_ of $frak(p)$ relative to the
extension $L slash K$. #idx("decomposition group")The groups ${G_(frak(p)_i)}$
are mutually conjugate in $G$. Each $sigma in G_frak(p)$ induces a
$K_P$-automorphism $hat(sigma)$ of the $frak(p)$-adic completion $L_frak(p)$,
since $sigma$ maps each Cauchy sequence from $L$ (relative to the $frak(p)$-adic
valuation) onto another such sequence. The #source(284)map $sigma -> hat(sigma)$
yields an isomorphism
$
  G_frak(p) tilde.equiv Gal(L_frak(p) slash K_P).
$ <eq:decomposition-group-galois>
We define
$
  n_P = (L_frak(p) : K_P) = italic("local degree") "of" L slash K "at" P.
$ <eq:local-degree>
#idx("local degree (of field extension)")
Then
$
  n_P = |G_frak(p)|, quad "and" n_P | (L : K) "for each" P.
$ <eq:local-degree-divides-degree>
It should be remarked that the fields ${L_(frak(p)_i) : 1 <= i <= g}$ are
mutually $K_P$-isomorphic, so $n_P$ does not depend on the choice of the prime
$frak(p)$ of $L$ which extends $P$.

The next theorem is of fundamental importance for the entire theory of simple
algebras over global fields. The proof depends on class field theory, and is
beyond the scope of this book. Proofs may be found in Cassels–Fröhlich
[@bib:Cassels1967], Janusz [@bib:Janusz1973], Neukirch [@bib:Neukirch1969], and
Weil [@bib:Weil1967].

#theorem(title: "Hasse Norm Theorem")[
  Let $L$ be a finite _cyclic_ extension of the global field $K$, and let
  $a in K$. For each prime $P$ of $K$, we choose a prime $frak(p)$ of $L$ which
  extends $P$. Then
  $
    a in N_(L slash K) (L) <==> a in N_(L_frak(p) slash K_P) (L_frak(p))
    "for each" P.
  $
  #idx("Hasse Norm Theorem", target: [@th:hasse-norm])
] <th:hasse-norm>

#remark(kind: "Remarks", numbered: false)[
  + The theorem asserts that $a$ is a _global_ norm (from $L$ to $K$) if and
    only if at each $P$, $a$ is a _local_ norm (from $L_frak(p)$ to $K_P$).
  + If $frak(p)$ and $frak(p)'$ are primes of $L$, both of which extend $P$,
    then there is a $K_P$-isomorphism $L_frak(p) tilde.equiv L_(frak(p)')$, and
    therefore
    $
      N_(L_frak(p) slash K_P) (L_frak(p))
      = N_(L_(frak(p)') slash K_P) (L_(frak(p)')).
    $
    This shows that in determining local norms at $P$, it does not matter which
    prime $frak(p)$ of $L$ we use, provided only that $frak(p)$ is an extension
    of the valuation $P$ from $K$ to $L$.
  + By Exercise~@exc:global-norm-local-norm, every global norm is also a local
    norm at each $P$. The difficult part of the proof of Hasse's Norm Theorem is
    the converse: if $a in K$ is a local norm at each $P$, then $a$ is a global
    norm. In proving this, it is necessary to know that $a$ is a local norm at
    _every_ prime $P$ of $K$, including the infinite primes.
  + The theorem breaks down if we drop the hypothesis that $L slash K$ be
    cyclic. There are counterexamples even when $L slash K$ is abelian (see
    Cassels–Fröhlich [@bib:Cassels1967, Exercise~5]).
]

#corollary[
  Let $A = (L slash K, sigma, a)$ be a cyclic algebra, where
  $Gal(L slash K) = chevron.l sigma chevron.r$ and $a in K^*$. Then
  $A tilde.op K$ if and only if $A_P tilde.op K_P$ for each prime $P$ of $K$.
] <cor:cyclic-algebra-local-splitting>

#proof[
  #source(285)By @th:cyclic-algebra-properties,
  $
    A tilde.op K <==> a in N_(L slash K) (L^*).
  $
  On the other hand, we showed in @th:cyclic-algebra-extension that for each
  $P$,
  $
    A_P tilde.op (L_frak(p) slash K_P, sigma^k, a),
  $
  where $sigma^k$ is some generator of $Gal(L_frak(p) slash K_P)$. Therefore by
  @th:cyclic-algebra-properties,
  $
    A_P tilde.op K_P <==> a in N_(L_frak(p) slash K_P) (L_frak(p)^*).
  $
  The desired result now follows from the Hasse Norm Theorem.
]

Clearly, we could have deduced @th:hasse-norm from
@cor:cyclic-algebra-local-splitting, and so the next result may be regarded as a
generalization of the Hasse Norm Theorem. Historically, it was first proved by
use of @cor:cyclic-algebra-local-splitting.

#theorem(major: true, title: "Hasse–Brauer–Noether–Albert")[
  Let $A$ be a central simple $K$-algebra. Then
  $
    A tilde.op K <==> A_P tilde.op K_P "for each prime" P "of" K.
  $
  #idx(
    "Hasse–Brauer–Noether–Albert Theorem",
    target: [@th:hasse-brauer-noether-albert],
  )
] <th:hasse-brauer-noether-albert>

#proof[
  If $A tilde.op K$, then clearly $A_P tilde.op K_P$ for each $P$. We shall
  prove the converse by assuming that $A_P tilde.op K_P$ for each $P$, but that
  $m = index [A] > 1$, and obtaining a contradiction. By
  @cor:galois-splitting-field, there exists a finite galois extension
  $L slash K$ such that $L$ splits $A$, that is, $L times.o_K A tilde.op L$. Let
  $G = Gal(L slash K)$, let $p$ be some rational prime dividing $m$, and let $H$
  be a Sylow $p$-subgroup of $G$. Then $p divides.not [G : H]$, whereas $|H|$ is
  a power of $p$.

  It is well known from group theory that $H$ has a descending chain of
  subgroups
  $
    H = H_0 supset H_1 supset dots.c supset H_n = 1, quad
    [H_i : H_(i+1)] = p,
  $
  with $H_(i+1) normal H_i$ for each $i$. Let $E_i$ be the subfield of $L$ fixed
  by $H_i$, so $E_n = L$, and each $E_(i+1) slash E_i$ is a cyclic extension of
  degree $p$.
  $
    #subgroup-tower
  $
  Further,
  $
    (E_0 : K) = [G : H] equiv.not 0 (mod p).
  $
  Set $F = E_(n-1)$, so $L slash F$ is a cyclic extension of degree $p$.

  #source(286)Let us set $B = F times.o_K A$, a central simple $F$-algebra. Then
  $
    L times.o_F B tilde.equiv L times.o_K A tilde.op L,
  $
  so $L$ splits $B$. Hence by Exercise~@exc:cyclic-splitting-similar, $B$ is
  similar to a cyclic algebra $C = (L slash F, sigma, b)$, where
  $Gal(L slash F) = chevron.l sigma chevron.r$ and $b in F^*$. We intend to show
  that $B tilde.op F$, so it suffices for us to prove that $C tilde.op F$. By
  @cor:cyclic-algebra-local-splitting,
  $
    C tilde.op F <==> C_frak(p) tilde.op F_frak(p) "for every prime" frak(p)
    "of" F.
  $
  Given a prime $frak(p)$ of $F$, its restriction to $K$ is a prime $P$ of $K$,
  and we have
  $
    C_frak(p) tilde.op B_frak(p) & = F_frak(p) times.o_F B
                                   tilde.equiv F_frak(p) times.o_K A \
                                 & tilde.equiv F_frak(p) times.o_(K_P) A_P
                                   tilde.op F_frak(p).
  $
  This proves that $C$ splits locally everywhere, whence $C tilde.op F$, and so
  $B tilde.op F$. We have thus shown that $F$ splits the algebra $A$.

  Repeat the argument, using the cyclic extension $F slash E_(n-2)$ in place of
  $L slash F$. Then we find that $E_(n-2)$ also splits $A$. Continuing in this
  manner, we see that $E_0$ splits $A$. But then $m | (E_0 : K)$ by
  @th:splitting-field-matrix-embedding. This is impossible, since $p | m$ but
  $p divides.not (E_0 : K)$, and so the theorem is established.
]

#remark(kind: "Remarks")[
  + For each prime $P$ of $K$, there is a homomorphism $B(K) -> B(K_P)$, defined
    by $K_P times.o_K dot$. Let $[A] in B(K)$, and let $m_P$ be the local index
    of $A$ at $P$. Then $m_P = 1$ a.e., which means that $[A_P] = 1$ a.e. Hence
    there is a well defined homomorphism
    $
      B(K) -> dsum_P B(K_P).
    $
    The Hasse–Brauer–Noether–Albert Theorem is precisely the assertion that this
    map is monic.
  + A stronger result, due to Hasse, describes the image of $B(K)$ in
    $dsum B(K_P)$ by means of Hasse invariants. It can be shown (see references)
    that the following sequence is exact:
    $
      1 -> B(K) -> dsum_P B(K_P) stretch(->)^inv bold(Q) slash bold(Z)
      -> 0,
    $ <eq:hasse-exact-sequence>
    where _inv_ denotes the Hasse invariant map, computed locally on each
    component: $inv = dsum inv_(K_P)$.

    It follows from the exactness of @eq:hasse-exact-sequence that
    #display-variant(
      [@eq:hasse-exact-sequence],
      suffix: "a",
      $
        sum_P inv [A_P] = 0, quad [A] in B(K).
      $,
    ) <eq:sum-of-local-invariants>
    Of course, $inv [A_P] = 0$ if $P$ is a complex prime, while $inv [A_P] = 0$
    or $1/2$ if $P$ is a real prime. The exactness of @eq:hasse-exact-sequence
    also tells us that, other than @eq:sum-of-local-invariants, these are the
    _only_ conditions which the set of local invariants ${inv [A_P]}$ must
    #source(287)satisfy. In other words, suppose that we are given in advance
    any set of fractions ${x_P}$ from $bold(Q) slash bold(Z)$, such that
    $
      cases(
        x_P = 0 & "a.e.," quad sum x_P = 0,
        x_P = 0 & "if" P "is complex," quad x_P = 0 "or" 1/2 "if" P "is real".
      )
    $
    Then there exists a unique $[A] in B(K)$ such that
    $
      inv [A_P] = x_P "for all" P.
    $
  + Some authors prove the exactness of @eq:hasse-exact-sequence directly (see
    Cassels–Fröhlich [@bib:Cassels1967], Neukirch [@bib:Neukirch1969]), and then
    deduce @th:hasse-norm–@th:hasse-brauer-noether-albert as corollaries. To
    prove that @eq:hasse-exact-sequence is exact, one shows first that the
    following sequence is exact:
    $
      1 -> H^2 (G_(L slash K), L^*)
      -> dsum_P H^2 (G_(L_frak(p) slash K_P), L_frak(p)^*)
      stretch(->)^inv 1/n bold(Z) slash bold(Z) -> 0.
    $ <eq:cohomology-exact-sequence>
    Here, $L slash K$ is any finite _cyclic_ extension, and $n = (L : K)$; the
    direct sum extends over all primes $P$ of $K$, and for each such $P$, the
    prime $frak(p)$ is some prime of $L$ extending $P$. The isomorphism obtained
    in @th:crossed-products-brauer-group permits one to replace
    $H^2 (G_(L slash K), L^*)$ by $B(L slash K)$, and likewise for the terms in
    the direct sum. Finally, one proves #display-variant(
      [@eq:cohomology-exact-sequence],
      suffix: "a",
      $
        B(K) = union.big_L B(L slash K),
      $,
    ) <eq:brauer-group-union-cyclic>
    where $L$ ranges over all finite cyclic extensions of $K$. In
    @eq:brauer-group-union we proved a weaker version of
    @eq:brauer-group-union-cyclic, in which $L$ ranges over all finite _galois_
    extensions. By @th:central-simple-cyclic below, it suffices to consider only
    cyclic extensions. Formula @eq:brauer-group-union-cyclic can also be proved
    directly, without using the difficult @th:central-simple-cyclic[Theorem]. We
    may remark that if $L slash K$ is a finite galois extension, not necessarily
    cyclic, then the image of _inv_ in @eq:cohomology-exact-sequence may be a
    proper subgroup of $(1 slash n) bold(Z) slash bold(Z)$. For the proofs of
    the exactness of @eq:hasse-exact-sequence and @eq:cohomology-exact-sequence,
    the reader may consult the references listed above.
] <rem:hasse-invariants-global>

As a first application of @th:hasse-brauer-noether-albert, we give a simple
criterion for deciding whether a finite extension of the global field $K$ splits
a given central simple $K$-algebra.

#theorem[
  Let $A$ be a central simple $K$-algebra. For each prime $P$ of $K$, let
  $m_P = index [A_P]$. Let $L$ be any finite extension of $K$, not necessarily a
  galois extension. Then $L$ is a splitting field for $A$ if and only if for
  each prime $frak(p)$ of $L$,
  $
    m_P | (L_frak(p) : K_P),
  $ <eq:local-index-divides-local-degree>
  where $P$ is the restriction of $frak(p)$ to $K$.
] <th:splitting-field-local-criterion>

#proof[
  #source(288)If $P$ is the restriction to $K$ of a prime $frak(p)$ of $L$, then
  $
    L_frak(p) times.o_(K_P) A_P tilde.equiv L_frak(p) times.o_L (L times.o_K A).
  $
  Hence if $L$ splits $A$, then $L times.o_K A tilde.op L$, whence
  $L_frak(p) times.o_(K_P) A_P tilde.op L_frak(p)$, and so $L_frak(p)$ splits
  $A_P$. Then @eq:local-index-divides-local-degree holds, by
  @th:splitting-field-matrix-embedding.

  Conversely, suppose that @eq:local-index-divides-local-degree holds for each
  $frak(p)$. Then (for each $frak(p)$) $L_frak(p)$ splits $A_P$, by
  @cor:local-splitting-degree. It follows that the central simple $L$-algebra
  $L times.o_K A$ is split locally at every prime $frak(p)$ of $L$. Hence by the
  Hasse–Brauer–Noether–Albert Theorem @th:hasse-brauer-noether-albert,
  $L times.o_K A tilde.op L$. Therefore $L$ splits $A$, as claimed, and the
  theorem is proved.
]

A second important consequence of @th:hasse-brauer-noether-albert is

#theorem[
  Let $A$ be a central simple $K$-algebra with local indices ${m_P}$, where $P$
  ranges over the primes of $K$. Set
  $
    m' = lcm {m_P}.
  $
  Then $exp [A] = m'$.
] <th:exponent-from-local-indices>

#proof[
  By @th:hasse-brauer-noether-albert,
  $
    [A]^t = 1 "in" B(K) <==> [A_P]^t = 1 "in" B(K_P) "for each" P.
  $
  But $exp [A_P] = m_P$ by @eq:local-invariant-exponent, so $[A_P]^t = 1$ if and
  only if $m_P | t$. This proves that $[A]^t = 1$ if and only if $t$ is
  divisible by each $m_P$. Hence $exp [A] = m'$, as claimed.
]

We are going to prove below that whenever $K$ is a global field, we have
$
  index [A] = exp [A], quad [A] in B(K).
$
We shall also prove that each central simple $K$-algebra $A$ is in fact a
_cyclic_ algebra, so that @cor:cyclic-algebra-local-splitting and
@th:hasse-brauer-noether-albert say exactly the same thing. The proofs will
depend on the following result, whose proof is beyond the scope of this book:

#theorem(title: "Grunwald–Wang")[
  Let $P_1, dots, P_s$ be any set of distinct primes of the global field $K$.
  Let ${m_(P_i) : 1 <= i <= s}$ be positive integers, subject to the conditions:
  $m_P = 1$ if $P$ is complex, $m_P = 1$ or $2$ if $P$ is real, where $P$ ranges
  over the ${P_i}$. Let $n$ be any positive integer divisible by each $m_(P_i)$,
  $1 <= i <= s$. Then there exists a _cyclic_ extension $L slash K$ such that
  $
    (L : K) = n, quad (L_frak(p) : K_P) = m_P, quad P = P_1, dots, P_s,
  $
  where $frak(p)$ denotes any prime of $L$ extending $P$.
  #idx("Grunwald–Wang Theorem", target: [@th:grunwald-wang])
] <th:grunwald-wang>

#remark(kind: "Remarks", numbered: false)[
  + For the proof of the Grunwald–Wang theorem, see Artin–Tate #source(
      289,
    )\[@bib:Artin1967, Ch.~10\] or Neukirch [@bib:Neukirch1974]. Wang
    [@bib:Wang1950] gives the proof for the case where $K$ is an algebraic
    number field.
  + For any galois extension $L slash K$ and any prime $P$ of $K$, we know that
    $(L_frak(p) : K_P)$ must divide $(L : K)$, by
    @eq:local-degree-divides-degree. Hence if $L slash K$ has local degree $m_P$
    at $P$, for $P = P_1, dots, P_s$, then necessarily $(L : K)$ must be a
    multiple of $m'$, where
    $
      m' = lcm {m_(P_1), dots, m_(P_s)}.
    $
    Hence if we seek a galois extension $L slash K$ with prescribed local
    degrees ${m_P}$ at some preassigned finite set of primes ${P_i}$ of $K$,
    then $m'$ is the smallest possible value for $(L : K)$. The Grunwald–Wang
    theorem tells us that not only can we find such a _galois_ extension
    $L slash K$ of degree $m'$, but in fact there always exists a _cyclic_
    extension of degree $m'$, with the prescribed local degrees. Further, we can
    force $(L : K)$ to be any preassigned multiple of $m'$, if desired.
]

We are now ready to prove

#theorem(major: true)[
  Let $[A] in B(K)$ have local indices ${m_P}$. Then
  $
    index [A] = exp [A] = lcm {m_P}.
  $
] <th:index-equals-exponent>

#proof[
  We know that $m_P = 1$ except possibly at some finite set of primes
  ${P_1, dots, P_s}$ of $K$. We also know that $m_P = 1$ if $P$ is complex, and
  that $m_P = 1$ or $2$ if $P$ is real. Let $m' = lcm {m_P}$, so $m' = exp [A]$
  by @th:exponent-from-local-indices. If $m = index [A]$, then $m' | m$ by
  @th:exponent-divides-index.

  On the other hand, by the Grunwald–Wang Theorem, there exists a cyclic
  extension $L slash K$ such that
  $
    (L : K) = m', quad (L_frak(p) : K_P) = m_P, quad P = P_1, dots, P_s,
  $
  where as usual $frak(p)$ denotes a prime of $L$ extending $P$. Since the local
  degree $(L_frak(p) : K_P)$ is the same for each such $frak(p)$, and since
  $m_P = 1$ for $P != P_1, dots, P_s$, it follows from
  @th:splitting-field-local-criterion that $L$ splits $A$. But then
  $m | (L : K)$, by @th:splitting-field-matrix-embedding[(i)]. Therefore
  $m = m'$, and the theorem is proved.
]

#theorem(major: true)[
  Every central simple $K$-algebra is cyclic.
] <th:central-simple-cyclic>

#proof[
  Let $A$ be a central simple $K$-algebra, let $(A : K) = n^2$, and let ${m_P}$
  be the local indices of $A$. Since $(A_P : K_P) = n^2$, it follows that
  $m_P | n$ for each $P$. Further, $m_P = 1$ except (say) at $P_1, dots, P_s$.
  By @th:grunwald-wang it follows that we may find a cyclic extension
  $E slash K$ such that
  $
    (E : K) = n, quad (E_frak(p) : K_P) = m_P, quad P = P_1, dots, P_s.
  $
  Then $E$ splits $A$, and $(A : K) = (E : K)^2$. Hence, by
  Exercise~@exc:cyclic-algebra-from-splitting, we may conclude that $A$ is
  isomorphic to a cyclic algebra $(E slash K, sigma, a)$, where
  $Gal(E slash K) = chevron.l sigma chevron.r$ and $a in K^*$. This completes
  the proof.
]

#example(numbered: false)[
  #source(290)Let us determine some of the local Hasse invariants of the cyclic
  algebra $A = (L slash K, sigma, a)$, where
  $Gal(L slash K) = chevron.l sigma chevron.r$ and $a in K^*$. Let $P$ denote a
  prime of $K$, and $frak(p)$ an extension of $P$ to $L$. Then by
  @th:cyclic-algebra-extension we have
  $
    A_P tilde.op (L_frak(p) slash K_P, sigma^k, a),
  $
  where $k$ is the least positive integer such that $sigma^k$ lies in the
  decomposition group $G_frak(p)$ of $frak(p)$ relative to $L slash K$. Of
  course, $inv [A_P] = 0$ whenever $A_P tilde.op K_P$.
  + If $P$ is complex, or if both $P$ and $frak(p)$ are real, then
    $A_P tilde.op K_P$.
  + Suppose that $P$ is real, $frak(p)$ complex. By
    Exercise~@exc:real-skewfields we have
    $
      A_P & tilde.op K_P quad "if" quad a_P > 0, \
      A_P & tilde.op bold(H) quad "if" quad a_P < 0,
    $
    where $a_P$ represents the image of $a$ under the embedding $K -> K_P$. In
    the latter case, $inv [A_P] = 1/2$.
  + Let $P$ be a finite prime, and assume that $P$ is unramified in the
    extension $L slash K$. This is equivalent to assuming that
    $L_frak(p) slash K_P$ is unramified. Since
    $G_frak(p) = chevron.l sigma^k chevron.r$, we may choose $r in bold(Z)$
    relatively prime to the local degree $n_P = |G_frak(p)|$, such that
    $sigma^(k r)$ is the Frobenius automorphism of the extension
    $L_frak(p) slash K_P$. By @eq:hasse-invariant we obtain
    $
      inv [A_P] = r dot v_P (a) slash n_P,
    $
    where $v_P$ is the exponential $P$-adic valuation. If we reduce the fraction
    $r dot v_P (a) slash n_P$ to lowest terms, then $m_P$ is the denominator of
    the fraction thus obtained. In particular, we observe that $m_P = 1$
    whenever $v_P (a) = 0$. Thus, $m_P = 1$ for every finite prime $P$, except
    possibly those primes $P$ which ramify in $L slash K$, or which contain $a$.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

Throughout these exercises, let $A$ denote a central simple $K$-algebra, where
$K$ is a global field, and let $P$ range over the primes of $K$.

#exercise[
  Prove that either $A tilde.op K$, or else there are at least two primes of $K$
  which ramify in $A$. #hint[@exc:two-ramified-primes][Use
    @eq:sum-of-local-invariants]<hint:two-ramified-primes>.
] <exc:two-ramified-primes>

#exercise[
  Prove that no infinite primes of $K$ are ramified in $A$, if $index [A]$ is
  odd.
] <exc:odd-index-unramified-infinite>

#exercise[
  Let $L slash K$ be a galois extension, $frak(p)$ a prime of $L$ extending the
  prime $P$ of $K$. Let $G_frak(p)$ be the decomposition group of $frak(p)$
  relative to $L slash K$, and write
  $
    G = union.big_(i=1)^n G_frak(p) dot sigma_i, quad n = [G : G_frak(p)].
  $
  For $x in L$, let
  $
    f(x) = product_(i=1)^n sigma_i (x) in L.
  $
  #source(291)Prove that
  $
    N_(L_frak(p) slash K_P) (f(x)) = N_(L slash K) (x).
  $
  Deduce that if $a in K$ is a global norm (from $L$ to $K$), then $a$ is a
  local norm (from $L_frak(p)$ to $K_P$) at each $P$.
  #hint[@exc:global-norm-local-norm][
    $
      N_(L_frak(p) slash K_P) (f(x))
      = product_(rho in G_frak(p)) product_(i=1)^n rho sigma_i (x)
      = product_(sigma in G) sigma(x) = N_(L slash K) (x).
    $
  ] <hint:global-norm-local-norm>
] <exc:global-norm-local-norm>
