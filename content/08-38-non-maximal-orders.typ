#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/08-38-non-maximal-orders.typ": class-group-k0-square

== Non-maximal orders <sec:non-maximal-orders>

The term "non-maximal order" refers to an order which may be maximal or not.
This section is intended to serve as a guide to further study of orders, as well
as to indicate some generalizations to non-maximal orders of the material in
§§~@sec:ideal-class-groups–@sec:picard-groups. During the past fifteen years,
there have appeared numerous research articles on the theory of orders. There
are, however, relatively few books or lecture notes dealing with this topic. The
principal ones are as follows:

+ #source(350)The lecture notes by Roggenkamp, Huber-Dyson
  [@bib:Roggenkamp1970b] and Roggenkamp [@bib:Roggenkamp1970a] contain a
  systematic treatment of orders. The first of these references contains
  Chapters I–V of the list below, and overlaps the present book considerably; it
  also contains an extensive bibliography. The second volume (Chapters VI–X) is
  devoted to proofs of the major recent developments in the theory of orders, up
  to 1969. It has a small bibliography, supplementing that of the first volume.
  The chapter headings are these:
  #enum(
    numbering: "I.",
    [Preliminaries on rings and modules.],
    [Homological algebra.],
    [The Morita theorems and separable algebras.],
    [Maximal orders.],
    [The Higman ideal and extensions of modules.],
    [Modules over orders, one-sided ideals over maximal orders.],
    [Genera of lattices.],
    [Grothendieck groups.],
    [Special types of orders.],
    [The number of indecomposable lattices over orders.],
  )

+ The lecture notes by Swan–Evans [@bib:Swan1970] provide an elegant and largely
  self-contained treatment of many topics in the theory of orders. The authors
  presuppose a basic knowledge of homological algebra. In a few places, they use
  some results from Swan [@bib:Swan1968]. Chapter headings:
  #enum(
    numbering: "1.",
    [Introduction.],
    [Frobenius functors.],
    [Finiteness theorems.],
    [Results on $K_0$ and $G_0$.],
    [Maximal orders.],
    [Orders.],
    [$K_0$ of a maximal order.],
    [$K_1$ and $G_1$.],
    [Cancellation theorems.],
  )
  Appendix.

+ The survey article by Reiner [@bib:Reiner1970] contains an extensive summary
  (without proofs) of the principal results on orders, and a large bibliography.
  Section headings are as follows:
  #enum(
    numbering: "1.",
    [Introduction. Notation and definitions.],
    [General remarks. Jordan–Zassenhaus theorem.],
    [Extensions.],
    [Higman ideal.],
    [Representations over local domains.],
    [#source(351)Genus.],
    [Maximal orders.],
    [Further results on genera.],
    [Projective modules and relative projective modules.],
    [Grothendieck groups and Whitehead groups.],
    [Commutative orders and related results.],
    [Divisibility of modules.],
    [Hereditary orders.],
    [Finiteness of the number of indecomposable representations.],
    [Representations of specific groups and orders.],
    [Representation rings.],
    [Group rings.],
    [Algebraic number theory.],
    [Krull–Schmidt and Cancellation Theorems.],
  )

+ Chapter XI of Curtis–Reiner [@bib:Curtis1962], entitled "Integral
  Representations", is concerned with the theory of orders.

+ There are two major references which deal primarily with maximal orders. The
  first, by Deuring [@bib:Deuring1935], has an extensive bibliography covering
  research before 1935. The exposition is self-contained but succinct. Chapter
  headings are:
  #enum(
    numbering: "I.",
    [Grundlagen.],
    [Die Struktursätze.],
    [Darstellungen der Algebren durch Matrizes.],
    [Einfache Algebren.],
    [Faktorensysteme.],
    [Theorie der ganzen Grössen.],
    [Algebren über Zahlkörpern. Zusammenhang mit der Arithmetik der Körper.],
  )

  The second reference is Weil [@bib:Weil1967]. This work is self-contained,
  except that familiarity with Haar measure is assumed. Chapters are:
  #enum(
    numbering: "I.",
    [Locally compact fields.],
    [Lattices and duality over local fields.],
    [Places of $bold(A)$-fields.],
    [Adeles.],
    [Algebraic number fields.],
    [The theorem of Riemann–Roch.],
    [Zeta-functions of $bold(A)$-fields.],
    [#source(352)Traces and norms.],
    [Simple algebras.],
    [Simple algebras over local fields.],
    [Simple algebras over $bold(A)$-fields.],
    [Local classfield theory.],
    [Global classfield theory.],
  )

In the present book, the following sections contain material on non-maximal
orders: §§~@sec:radicals-of-rings, @sec:orders-definitions-and-examples,
@sec:maximal-orders-local-case, @sec:ideal-classes, @sec:genus,
@sec:k0-of-maximal-orders–@sec:group-rings.

We shall now sketch a generalization of the results in
§§~@sec:ideal-class-groups–@sec:picard-groups to the case of non-maximal orders.
For the remainder of this section, let $Lambda$ be an $R$-order, maximal or not,
in a separable $K$-algebra $A$. As usual, $R$ denotes a Dedekind domain with
quotient field $K$. Since $Lambda$ need not decompose into a direct sum of
orders in simple algebras, we may no longer restrict our attention to the case
of central simple algebras.

Recall from §~@sec:genus that two left $Lambda$-lattices $M, N$ are in the same
_genus_ (notation: $M samegenus N$) if $M_P tilde.equiv N_P$ as left
$Lambda_P$-lattices, for each maximal ideal $P$ of $R$. By
@th:local-completion-comparison[(iii)], in this definition it is immaterial
whether the subscript $P$ denotes localization or completion. Call $M$ _locally
free_#idx("locally free module") (of rank $n$) if $M samegenus Lambda^((n))$.
(If $Lambda$ is maximal, then by @th:separable-maximal-principal _every_ left
$Lambda$-ideal $M$ in $A$, such that $K M = A$, is locally free of rank 1. More
generally, any left $Lambda$-lattice $X$, such that $K X tilde.equiv A^((n))$,
is locally free of rank $n$ by @th:lattice-free-plus-ideal.)

Whether or not $Lambda$ is a maximal order, we shall define the _locally free
class group_#idx("locally free class group")#idx("class group")#idx(
  "ideal",
  "class",
) of $Lambda$, denoted by $Cl Lambda$, as follows: the elements of $Cl Lambda$
are stable isomorphism classes $[M]$ of locally free left $Lambda$-lattices $M$
in $A$ (see Exercise~@exc:stable-same-genus). As in @eq:ideal-sum-decomposition,
we define addition of classes thus: given $M$, $M' samegenus Lambda$, by
@cor:genus-addition there exists an $M'' samegenus Lambda$ such that
$M dotplus M' tilde.equiv Lambda dotplus M''$. We then set $[M] + [M'] = [M'']$.
To show that inverses exist in $Cl Lambda$, we need only modify the proof of
@th:stable-class-group by using Exercises~@exc:genus-direct-sum
and~@exc:genus-multiple-sum in the parts of the proof where we previously used
@th:left-ideals-genus[Theorem] and @th:lattice-free-plus-ideal[Theorem].

The results in @th:eichler-ray-classes–@th:swan-class-group need not be true for
non-maximal orders. Before stating Jacobinski's generalization of these results,
we introduce the following definition:

#definition[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, where $R$ is a
  Dedekind domain and $K$ is a global field. For each simple component $A_i$ of
  $A$, let $R_i$ denote the integral closure of $R$ in the center of $A_i$. We
  say that _$A$ satisfies the Eichler condition relative to $R$_ (notation:
  $A = eichler(R)$) if for each $i$, $A_i = eichler(R_i)$. This definition
  extends that given in @def:eichler-condition. #idx(
    "Eichler condition",
    target: [@def:eichler-condition-separable],
  )#idx("Eichler/$R$", target: [@def:eichler-condition-separable])
] <def:eichler-condition-separable>

#remark(numbered: false)[
  Let $R = algint {K}$, where $K$ is an algebraic number field, and let $G$ be a
  finite group. Set $A = K G$, the group algebra of $G$ over $K$. Following
  #source(353)the approach in Swan–Evans [@bib:Swan1970], we may give some
  _sufficient_ conditions that $A = eichler(R)$. Indeed, if $A != eichler(R)$,
  then some simple component $A_i$ of $A$ must be a totally definite quaternion
  algebra over its center $L$. Since this can never occur if $L$ has any complex
  primes, we deduce
  + _If $K$ has any complex primes, then $A = eichler(R)$._

  Next, suppose that $A_i$ is a totally definite quaternion algebra; then its
  completion at each real prime of $L$ must be the quaternions $bold(H)$ over
  the real field $bold(R)$. Thus the composition of maps
  $
    K G = A -> A_i -> bold(H)
  $
  gives a homomorphism of $G$ onto a subgroup $overline(G)$ of $u(bold(H))$, and
  necessarily $bold(H)$ equals $bold(R) overline(G)$. Surely $overline(G)$ must
  be nonabelian, since $bold(H)$ is a noncommutative ring.

  The nonabelian finite subgroups $overline(G)$ of $u(bold(H))$ are known
  explicitly (see Coxeter [@bib:Coxeter1940], Coxeter–Moser [@bib:Coxeter1957]),
  and are as follows:
  $
    cases(
      #[generalized quaternion group of order $4n$, $n >= 2$,],
      #[binary tetrahedral group $chevron.l 2, 3, 3 chevron.r$ of order 24,],
      #[binary octahedral group $chevron.l 2, 3, 4 chevron.r$ of order 48,],
      #[binary icosahedral group $chevron.l 2, 3, 5 chevron.r$ of order 120.],
    )
  $
  Hence we conclude
  #enum(start: 2, [_$A = eichler(R)$ if $G$ has no homomorphic image in the
  above list._])
]

We now state without proof:

#theorem(title: [Jacobinski [@bib:Jacobinski1968a, @bib:Jacobinski1968b]])[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, where $K$ is a
  global field, and where $A = eichler(R)$. Let $cal(S)$ be the finite set
  consisting of all maximal ideals $P$ of $R$ such that $Lambda_P$ is not a
  maximal $R_P$-order in $A_P$. Keeping the notation of
  @def:eichler-condition-separable, let $C = dsum R_i$, so $K C$ is the center
  of $A$. Denote by $I(C, cal(S))$ the multiplicative group of all $C$-lattices
  $J$ in $K C$ such that
  $
    K dot J = K C, quad J_P = C_P "for all" P in cal(S).
  $
  Let
  $
    P_Lambda (C) = {C dot nr_(A slash K C) x : x in A, x in u(Lambda_P)
      "for all" P in cal(S)},
  $
  a subgroup of $I(C, cal(S))$ consisting of certain principal $C$-ideals in
  $K C$. Then the locally free class group $Cl Lambda$ satisfies
  $
    Cl Lambda tilde.equiv I(C, cal(S)) slash P_Lambda (C).
  $ <eq:jacobinski-class-group>
  Furthermore, if $M, N$ are $Lambda$-lattices in the same genus as $Lambda$,
  then
  $
    [M] = [N] quad "in" Cl Lambda <==> M tilde.equiv N.
  $ <eq:jacobinski-cancellation>
] <th:jacobinski-class-group>

#remark(kind: "Remarks")[
  + If $Lambda$ is maximal, the set $cal(S)$ may be taken to be the empty
    #source(354)set. The isomorphism occurring in @eq:jacobinski-class-group can
    then be described componentwise, according to the simple components of $A$.
    At each simple component, we obtain precisely the isomorphism given in
    @th:swan-class-group.
  + In the preceding theorem, the subscript $P$ denotes completion. The result
    holds equally well if we use localizations rather than completions.
  + An idele-theoretic version of this theorem, due to Fröhlich
    [@bib:Frohlich1975], holds even when $A != eichler(R)$. See also Wilson
    [@bib:Wilson1977].
  + $Cl Lambda$ is a finite group by virtue of the
    @th:jordan-zassenhaus[Jordan–Zassenhaus Theorem].
] <rem:jacobinski-class-group>

Let us turn next to the material in §~@sec:k0-of-maximal-orders. The definition
of $K_0 (Lambda)$ given in §~@sec:k0-of-maximal-orders holds for all _rings_
$Lambda$, and hence surely for all orders $Lambda$, maximal or not. The map
$mu : Cl Lambda -> K_0 (Lambda)$ occurring in @eq:k0-exact-sequence is monic,
whether or not $Lambda$ is maximal. However, the sequence @eq:k0-exact-sequence
need not be exact, and @eq:k0-structure need not hold true.

Now let $Gamma = M_n (Lambda)$, and keep the notation of @th:k0-matrix-order.
Most of the proof of @th:k0-matrix-order remains valid when $Lambda$ is any
$R$-order in a separable $K$-algebra. It shows that, in the notation of
@eq:k0-morita-diagram, there is a commutative diagram
$
  #class-group-k0-square
$ <eq:class-group-k0-square>
where $mu, mu'$ are monic, and where $phi, L times.o_Lambda dot$ are
isomorphisms. As a consequence of the above, we have

#corollary[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, where $K$ is an
  algebraic number field. Let $Gamma = M_2 (Lambda)$, $B = K Gamma = M_2 (A)$.
  Let $C$, $cal(S)$ be as in @th:jacobinski-class-group. Then whether or not
  $A = eichler(R)$, we have
  $
    Cl Lambda tilde.equiv Cl Gamma tilde.equiv I(C, cal(S)) slash P_Gamma (C).
  $
] <cor:class-group-matrix-order>

#proof[
  Since $K$ is an algebraic number field, it follows that $B = eichler(R)$ even
  if $A != eichler(R)$. The ring $C$ and the set $cal(S)$ are the same for
  $Gamma$ as for $Lambda$. The formula for $Cl Gamma$ is just the one given by
  @eq:jacobinski-class-group, with $Gamma$ in place of $Lambda$.
]

All of the material in §~@sec:picard-groups, up to and including
@th:picent-commutative-semilocal, is valid for arbitrary $R$-orders (and indeed
for _$R$-algebras_). The important results
@th:picent-ideal-sequence–@th:normalizer-outcent, and the fundamental
@th:picent-local-global, were established in §~@sec:picard-groups for all
$R$-orders, maximal or not. Of course, @cor:normalizer-dvr[Theorem],
@th:picent-complete-local[Theorem] and @cor:picent-maximal-order[Theorem] hold
only for the case of maximal orders.

It is possible to salvage @th:picent-to-class-group, by introducing the _locally
free Picard group_#idx("locally free Picard group") $LFP(Lambda)$#idx(
  "LFP",
). This is the subgroup of $Picent Lambda$ consisting of all
$(X) in Picent Lambda$ such #source(355)that $X$ is locally free as left
$Lambda$-module. (Such $X$'s are necessarily of rank 1.) By
Exercise~@exc:locally-free-bimodule-invertible, $LFP(Lambda)$ is indeed a group,
and consists of all bimodule isomorphism classes $(X)$, where $X$ ranges over
all two-sided $Lambda$-submodules of $A$ such that $X samegenus Lambda$ as left
$Lambda$-modules. (Each such $X$ is necessarily an invertible bimodule, by
Exercise~@exc:locally-free-bimodule-invertible.)

If $Lambda$ is a maximal order, then
$
  LFP(Lambda) = Picent Lambda
$
by @th:separable-maximal-principal. This also holds true whenever $Lambda$ is
commutative, but not necessarily maximal, by virtue of
@th:picent-commutative-semilocal.

Returning to arbitrary orders, consider the map
$omega : Outcent Lambda -> Picent Lambda$. Clearly its image lies in
$LFP(Lambda)$, and hence there is a monomorphism
$
  omega : Outcent Lambda -> LFP(Lambda),
$
with $omega(f) = (lmodule(1, Lambda)_f)$. It follows at once from
@th:left-isomorphic-invertible that for $(X), (Y) in LFP(Lambda)$,
$
  lmodule(Lambda, X) tilde.equiv lmodule(Lambda, Y) <==>
  (Y) in (X) dot im omega.
$ <eq:lfp-left-isomorphism>
Furthermore, since $LFP(C) = Picent C$, we deduce from @eq:picent-local-global
that there is an exact sequence
$
  1 -> LFP(C) stretch(->)^tau LFP(Lambda)
  -> product_P LFP(Lambda_P) -> 1,
$ <eq:lfp-exact-sequence>
with $LFP(Lambda_P) = 1$ a.e. Finally, we have
$
  LFP(Lambda_P) & = {(X) in Picent Lambda_P :
                    X tilde.equiv Lambda_P "as left" Lambda_P"-modules"} \
                & tilde.equiv Outcent Lambda_P.
$

Generalizing @th:picent-to-class-group, we prove

#theorem(title: [Fröhlich–Reiner–Ullom [@bib:Frohlich1974]])[
  For any $R$-order $Lambda$ in a separable $K$-algebra $A$, there is a
  homomorphism
  $
    theta : LFP(Lambda) -> Cl Lambda,
  $
  given by $theta(X) = [X]$, $(X) in LFP(Lambda)$. Furthermore, suppose
  that#footnote[This hypothesis is satisfied whenever $K$ is a global field and
    $A = eichler(R)$, by virtue of @eq:jacobinski-cancellation. It also holds
    for arbitrary $K$ when $Lambda$ is a commutative order, by virtue of
    @th:kaplansky-commutative-cancellation below.] for left $Lambda$-lattices
  $M, N$ in the genus of $Lambda$,
  $
    [M] = [N] <==> M tilde.equiv N.
  $ <eq:genus-stable-cancellation>
  Then
  $
    ker theta tilde.equiv Outcent Lambda.
  $
] <th:lfp-class-group>

#proof[
  The first half of the proof of @th:picent-to-class-group carries over
  unchanged, and shows that $theta$ is a well defined homomorphism. Now assume
  that @eq:genus-stable-cancellation holds true, #source(356)and let
  $(M) in LFP(Lambda)$. Then
  $
    theta(M) = 0 <==> [M] = [Lambda] quad "in" Cl Lambda <==>
    lmodule(Lambda, M) tilde.equiv lmodule(Lambda, Lambda).
  $
  But $lmodule(Lambda, M) tilde.equiv lmodule(Lambda, Lambda)$ if and only if
  $(M) in im omega$, by @eq:lfp-left-isomorphism. This shows that
  $ker theta = im omega$, whence $ker theta tilde.equiv Outcent Lambda$ as
  claimed.
]

#corollary[
  For any commutative $R$-order $Lambda$ in a separable $K$-algebra $A$, we have
  $
    Picent Lambda = LFP(Lambda) tilde.equiv Cl Lambda.
  $
] <cor:commutative-picent-class-group>

#proof[
  We shall identify the set of left $Lambda$-modules with the set of
  $(Lambda, Lambda)$-bimodules over $Lambda$; this can be done since $Lambda$ is
  commutative. We have already remarked that $Picent Lambda = LFP(Lambda)$, by
  @th:picent-commutative-semilocal. Let us now show that $theta$ is an
  isomorphism. By @th:lfp-class-group, we have
  $ker theta tilde.equiv Outcent Lambda = 1$, so $theta$ is monic. Further, each
  element of $Cl Lambda$ is of the form $[M]$, for some locally free
  $Lambda$-lattice $M$ in $A$. By
  Exercise~@exc:locally-free-bimodule-invertible, $M$ is an invertible
  $(Lambda, Lambda)$-bimodule, and hence $(M) in LFP(Lambda)$. Clearly
  $theta(M) = [M]$, so $theta$ is epic. This completes the proof of the
  corollary.
]

In the preceding discussion we made use of the following result, which is of
independent interest.

#theorem(title: "Kaplansky")[
  Let $R$ be any noetherian domain with quotient field $K$, let $Lambda$ be any
  commutative $R$-order in a $K$-algebra $A$ (not necessarily separable over
  $K$). By a "$Lambda$-ideal in $A$" we mean a finitely generated
  $Lambda$-submodule $M$ of $A$ such that $K M = A$.
  + Let $M_1, dots, M_t, N_1, dots, N_t$ be $Lambda$-ideals in $A$ such that
    $
      M_1 dotplus dots.c dotplus M_t tilde.equiv N_1 dotplus dots.c dotplus N_t
      quad "as" Lambda"-modules."
    $
    Then
    $
      M_1 dots.c M_t tilde.equiv N_1 dots.c N_t quad "as" Lambda"-modules,"
    $
    where these products are computed within $A$.
  + Two $Lambda$-ideals in $A$ are stably isomorphic if and only if they are
    isomorphic.
] <th:kaplansky-commutative-cancellation>

#proof[
  (i) The hypotheses imply that for all $i, j$ between 1 and $t$,
  $
    Hom_A (K M_i, K N_j) tilde.equiv K times.o_R Hom_Lambda (M_i, N_j).
  $
  Furthermore, the map
  $
    Hom_Lambda (M_i, N_j) -> Hom_A (K M_i, K N_j)
  $
  is monic.

  #source(357)Now let $phi : dsum M_i tilde.equiv dsum N_j$ be a
  $Lambda$-isomorphism. Then $phi$ can be extended to an $A$-isomorphism
  $phi_* : A^((t)) tilde.equiv A^((t))$. Hence there exists an invertible matrix
  $mu = (alpha_(i j)) in M_t (A)$ such that
  $
    phi(m_1, dots, m_t) = (alpha_(i j)) (m_1, dots, m_t)^T, quad m_i in M_i,
    quad 1 <= i <= t,
  $
  where $T$ denotes "transpose". Therefore
  $
    alpha_(i j) M_j subset N_i, quad 1 <= i, j <= t.
  $
  Set $d = det mu$; then $d in u(A)$ since $mu$ is invertible. Furthermore, $d$
  is a sum of products of the form
  $
    plus.minus alpha_(pi(1), 1) dots.c alpha_(pi(t), t),
  $
  where $pi$ is a permutation on ${1, dots, t}$. It follows from these
  inclusions that
  $
    d dot M_1 dots.c M_t subset N_1 dots.c N_t.
  $

  On the other hand, $phi^(-1)$ also extends to an $A$-isomorphism
  $(phi^(-1))_* : A^((t)) tilde.equiv A^((t))$, described by the matrix
  $mu^(-1)$ of determinant $d^(-1)$. The above reasoning shows that
  $
    d^(-1) dot N_1 dots.c N_t subset M_1 dots.c M_t.
  $
  Therefore $product N_i = d dot product M_i$, whence
  $product N_i tilde.equiv product M_i$ as claimed.

  (ii) Now let $M$, $N$ be $Lambda$-ideals in $A$ which are stably isomorphic.
  Then $M dotplus Lambda^((r)) tilde.equiv N dotplus Lambda^((r))$ for some $r$,
  whence $M tilde.equiv N$ by (i). This completes the proof of the theorem.
]

To conclude this section, we give the following generalization of
@th:picent-matrix-order:

#theorem[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra $A$, where $R$ is a
  Dedekind domain. Assume#footnote[See footnote to @th:lfp-class-group.] that
  condition @eq:genus-stable-cancellation holds, that is, stable isomorphism
  implies isomorphism for locally free left $Lambda$-lattices. Let $n >= 1$, and
  set $E = M_n (R)$, $Gamma = E times.o_R Lambda tilde.equiv M_n (Lambda)$, as
  in @th:picent-matrix-order. Then all of the assertions (i)–(iii) in
  @th:picent-matrix-order remain true, provided that in @eq:picent-class-ladder
  we replace $Picent$ by $LFP$. Furthermore,
  @cor:matrix-outer-automorphisms[(i)] holds true in this case.
] <th:lfp-matrix-order>

#proof[
  The proofs of @eq:picent-class-ladder and @cor:matrix-outer-automorphisms
  carry over with only minor modifications. We omit the details.
]

It is worth pointing out a stronger version of
@cor:matrix-outer-automorphisms[(ii)], namely

#corollary[
  Let $Lambda$ be a commutative $R$-order in a separable $K$-algebra $A$. Then
  $
    Outcent M_n (Lambda) tilde.equiv (Cl Lambda)_n
  $
  for each $n >= 1$.
] <cor:outcent-matrix-commutative>

#proof[
  #source(358)By @cor:commutative-picent-class-group $theta$ is an isomorphism,
  whence $cok theta = 0$. Further, $Outcent Lambda = 1$ since $Lambda$ is
  commutative. The desired result now follows from the exactness of the sequence
  @eq:outcent-cokernel-sequence asserted in @th:lfp-matrix-order.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

In the following, $Lambda$ is an $R$-order in a separable $K$-algebra $A$, where
$R$ is a Dedekind domain.

#exercise[
  Prove that stably isomorphic left $Lambda$-lattices are in the same genus.
  #hint[@exc:stable-same-genus][Let $X$, $Y$ be $Lambda$-lattices such that
    $
      X dotplus Lambda^((r)) tilde.equiv Y dotplus Lambda^((r)).
    $
    Complete at an arbitrary $P$, then show that $X_P tilde.equiv Y_P$ by
    Exercise~@exc:cancellation.] <hint:stable-same-genus>
] <exc:stable-same-genus>

#exercise[
  Prove that every locally free left $Lambda$-lattice is $Lambda$-projective.
  #hint[@exc:locally-free-projective][See @cor:projective-local.]
  <hint:locally-free-projective>
] <exc:locally-free-projective>

#exercise[
  Let
  $
    N(Lambda) = {x in u(A) : x Lambda x^(-1) = Lambda},
  $
  the _normalizer_ of $Lambda$ in $A$. Show that
  $
    N(Lambda) = {x in u(A) : x Lambda x^(-1) subset Lambda}.
  $
  #hint[@exc:normalizer-inclusion][Let $x in u(A)$ be such that
    $x Lambda subset Lambda x$. By Exercise~@exc:order-ideal-norm,
    $
      ord_R Lambda slash x Lambda = ord_R Lambda slash Lambda x.
    $
    Hence $x Lambda = Lambda x$ by @th:order-ideal-multiplicative.]
  <hint:normalizer-inclusion>
] <exc:normalizer-inclusion>

#exercise[
  Let $X$ be a two-sided $Lambda$-submodule of $A$. Show that if $X$ is locally
  free as left $Lambda$-module, then $X samegenus Lambda$ and $X$ is an
  invertible bimodule whose inverse is also locally free. Deduce from this that
  $LFP(Lambda)$ is a subgroup of $Picent Lambda$.
  #hint[@exc:locally-free-bimodule-invertible][If $X samegenus Lambda^((n))$
    then $K X tilde.equiv A^((n))$, so $n = 1$ and $X samegenus Lambda$. Now put
    $Y = {a in A : X a subset Lambda}$, another bimodule in $A$. To prove that
    $X$ is invertible, we need only show that $X Y = Y X = Lambda$. It suffices
    to verify this after passing to completions. Changing notation, assume that
    $R$ is complete and that $X = Lambda u$, where $u in u(A)$. Then
    $Lambda u dot Lambda = Lambda u$ since $X$ is a bimodule, whence
    $u Lambda subset Lambda u$. Thus $u Lambda = Lambda u$ by
    Exercise~@exc:normalizer-inclusion, and hence
    $Y = u^(-1) Lambda = Lambda u^(-1)$.]
  <hint:locally-free-bimodule-invertible>
] <exc:locally-free-bimodule-invertible>

#exercise[
  Let $R$ be a principal ideal domain with quotient field $K$, and let
  $Gamma = M_n (R)$, where $n >= 1$. Show that every invertible matrix
  $x in M_n (K)$, such that $x Gamma x^(-1) = Gamma$, is of the form
  $x = alpha y$ for some nonzero $alpha in K$ and some $y in u(Gamma)$.
  #hint[@exc:matrix-order-normalizer][Take $Lambda = R$ in
    @cor:outcent-matrix-commutative to deduce that $Outcent Gamma = 1$. By
    @th:normalizer-outcent,
    $Outcent Gamma tilde.equiv N(Gamma) slash u(Gamma) u(K)$, where $N(Gamma)$
    is the normalizer of $Gamma$ in $K Gamma$. Hence
    $N(Gamma) = u(Gamma) u(K)$.] <hint:matrix-order-normalizer>
] <exc:matrix-order-normalizer>

#exercise[
  Let $G$ be a finite group, $R$ a Dedekind domain with quotient field $K$, and
  let $Lambda = R G$, $A = K Lambda = K G$. Suppose that $|G| != 0$ in $R$, and
  that no prime divisor of $|G|$ is a unit in $R$. A fundamental theorem due to
  Swan asserts that, in this case, every projective left $Lambda$-lattice is
  locally free. Deduce from this that there is a split exact sequence of
  additive groups
  #source(359)
  $
    0 -> Cl Lambda stretch(->)^mu K_0 (Lambda) stretch(->)^psi K_0 (A),
  $ <eq:locally-free-k0-sequence>
  where
  $
    mu[M] = [Lambda] - [M], [M] in Cl Lambda; quad
    psi[X] = [K times.o_R X], [X] in K_0 (Lambda).
  $
  #hint[@exc:swan-k0-sequence][Imitate the relevant parts of the proof of
    @th:k0-maximal-order[Theorem]. The sequence @eq:locally-free-k0-sequence
    splits, since $K_0 (A)$ is a free $bold(Z)$-module by
    Exercise~@exc:k0-semisimple.] <hint:swan-k0-sequence>
] <exc:swan-k0-sequence>
