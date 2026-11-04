#import "main-defs.typ": *
#import "statements.typ": *

== Dedekind domains <sec:dedekind-domains>

#source(53)Throughout this section $R$ denotes an integral domain with quotient
field $K$. To avoid trivialities, we assume always that $R != K$. We shall
define Dedekind domains and shall state, without proof or detailed references,
some of their most important properties. Proofs and complete expositions are
readily available in texts such as Curtis–Reiner [@bib:Curtis1962], Janusz
[@bib:Janusz1973], O'Meara [@bib:OMeara1963], Ribenboim [@bib:Ribenboim1972],
Samuel [@bib:Samuel1967], Weiss [@bib:Weiss1963], Zariski–Samuel
[@bib:Zariski1958].

From the standpoint of ideal theory, Dedekind domains are the simplest type of
domain beyond principal ideal domains, and share many of their arithmetical
properties. Dedekind domains arise naturally, as follows: let $R$ be a principal
ideal domain with quotient field $K$, let $L$ be a finite extension of $K$, and
let $S$ be the integral closure of $R$ in $L$. Then $S$ is a Dedekind domain
with quotient field $L$. As a matter of fact (see
@th:integral-closure-dedekind), this same conclusion holds under the weaker
hypothesis that $R$ itself is a Dedekind domain.

We may also remark that Dedekind domains are a special kind of maximal order.
One of the main topics of this book is the study of arithmetical properties of
maximal orders analogous to those of Dedekind domains. Many of the results
stated in this section are special cases of the theorems to be developed in
Chapter~@ch:maximal-orders-over-dedekind-domains.

Let us fix some notation, to be used throughout this section. The _annihilator_
of an $R$-module $M$ is defined by
#idx("annihilator")
$
  ann_R M = {a in R : a dot M = 0}.
$
Likewise we set
$
  ann_R m = {a in R : a dot m = 0},
$
for $m in M$. Call $m in M$ an _$R$-torsion_ element if $ann_R m != 0$. The set
of all $R$-torsion elements of $M$ is the _$R$-torsion submodule_ of $M$, and is
the kernel of the $R$-homomorphism $M -> K times.o_R M$ given by
$m -> 1 times.o m$, $m in M$ (see §~@ss:modules-of-quotients). #idx(
  "torsion element",
)#idx("torsion submodule")

The _$R$-rank_ of $M$ is defined as
#idx("rank")
$
  rank_R M = dim_K (K times.o_R M).
$
We call $M$ _$R$-torsionfree_ if $M$ contains no torsion element except 0. In
this case, we may identify $M$ with its image $1 times.o M$ in $K times.o_R M$;
we may then write $K times.o_R M$ in the simpler form $K dot M$, where $K dot M$
denotes the set of all finite sums ${sum a_i m_i : a_i in K, m_i in M}$. In the
same way, for each ring of quotients $R'$ of $R$, the $R$-torsionfree $R$-module
$M$ is embedded in the $R'$-module $R' times.o_R M$; after making the obvious
identification, we may denote $R' times.o_R M$ by $R' dot M$.
#idx("torsionfree")

An _$R$-lattice_ is a finitely generated $R$-torsionfree $R$-module. Each
$R$-lattice $M$ is an $R$-submodule of a finite dimensional vector space $V$
over $K$, namely $V = K dot M$. We call $M$ a _full_ $R$-lattice in $V$, the
adjective indicating that $M$ contains a $K$-basis of $V$. Let $M$ and $N$ be a
pair of full $R$-lattices in a #idx("lattice")#idx("full lattice") #source(
  54,
)$K$-space $V$. Since $N$ contains a $K$-basis for $V$, it is clear that for
each $x in M$ there is a nonzero $r in R$ such that $r dot x in N$. But $M$ is
finitely generated as $R$-module. Therefore we can choose $r in R$, $r != 0$,
such that $r dot M subset N$.

Let $M$ be an $R$-lattice, and let $N$ be a sublattice of $M$. We shall call $N$
an _$R$-pure_ sublattice of $M$ if $M slash N$ is $R$-torsionfree. Equivalently,
$N$ is $R$-pure in $M$ if for each nonzero $alpha in R$,
#idx("pure")
$
  N inter alpha M = alpha N.
$
Let $S$ be the multiplicative set $R - {0}$. Then $M slash N$ is $R$-torsionfree
if and only if $N$ is an $S$-saturated#footnote[This concept has been defined
  immediately preceding @th:saturated-correspondence.] $R$-submodule of $M$. As
a special case of @th:saturated-correspondence, we thus obtain

#theorem(zeroth: true)[
  Let $M$ be an $R$-lattice. There is a one-to-one inclusion-preserving
  correspondence $N <-> W$ between the set of $R$-pure sublattices $N$ of $M$,
  and the set of $K$-subspaces $W$ of $K M$, given by
  $
    W = K N, quad N = W inter M.
  $
] <th:pure-sublattices>

=== Ideal theory, modules, order ideals <ss:ideal-theory-modules>

Let $R$ be an integral domain with quotient field $K$. We call $R$ a _Dedekind
domain_ if it satisfies any one of the following three equivalent conditions:
#idx("Dedekind domain")

#condition[
  $R$ is a hereditary ring, that is, every ideal of $R$ is a projective
  $R$-module (see §~@ss:hereditary-rings).
] <def:dedekind-hereditary>

#condition[
  $R$ is a noetherian integrally closed domain such that every nonzero prime
  ideal of $R$ is a maximal ideal.
] <def:dedekind-noetherian>

#condition[
  Every proper nonzero ideal of $R$ is uniquely expressible as a product of
  nonzero prime ideals of $R$, apart from order of occurrence of the factors.
] <def:dedekind-factorization>

We recall that $R$ is _noetherian_ if its ideals satisfy the A.C.C. (see
@th:noetherian-equivalences). The ring $R$ is _integrally closed_ if each
element of $K$ integral over $R$ necessarily lies in $R$. A _prime ideal_ of $R$
is an ideal $J$ properly contained in $R$ (notation: $J < R$) such that
$R slash J$ has no zero divisors (see @def:proper-maximal-prime). For the proof
that these three conditions are equivalent, and also for the proofs of theorems
stated below, the reader may consult the references listed at the beginning of
§~@sec:dedekind-domains. We shall seldom specify the exact location in these
references where the proofs may be found.

#theorem[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $L$ be any field
  extension of $K$ of finite degree. Then the integral closure of $R$ in $L$ is
  a Dedekind domain $S$ with quotient field $L$.
] <th:integral-closure-dedekind>

#source(55)
#remark(kind: "Remarks", numbered: false)[
  + Recall from §~@sec:integral-closure that $S$ consists of all elements of $L$
    which are zeros of monic polynomials in $R[X]$. By @cor:sum-product-integral
    we know that $S$ is a ring. The assertion that $S$ is a Dedekind domain
    contains the additional information that $S$ is integrally closed. We may
    also point out that each $x in L$ is expressible as a quotient
    $x = y slash r$ with $y in S$, $r in R$; namely, we need only choose $r$ to
    be a multiple of the denominators of the coefficients which occur in
    $minpol_K x$.
  + The integral closure of $R$ in $K$ is $R$ itself, since $R$ is integrally
    closed.
  + Clearly $S$ is a torsionfree $R$-module, since $R$ is a subring of the
    integral domain $S$.
  + Let $K$ be an _algebraic number field_, that is, a finite extension of the
    rational field $bold(Q)$. By @th:integral-closure-dedekind, the integral
    closure of $bold(Z)$ in $K$ is a Dedekind domain, hereafter denoted by
    $algint {K}$. Its elements are called _algebraic integers_. #idx(
      "algebraic number field",
    )#idx("alg. int.")
  + In many texts, @th:integral-closure-dedekind[Theorem] is proved only when
    $L$ is separable over $K$. For the general version, see Zariski–Samuel
    [@bib:Zariski1958, Chapter~V, §~8, Theorem~19].
]

Let $L$ be a finite field extension of $K$, and let $T_(L slash K)$ be the trace
map from $L$ to $K$, defined as in §~@ss:min-char-pol. From $T$ we can construct
a bilinear _trace form_ $tau: L times L -> K$ by setting
#idx("trace form")
$
  tau(x, y) = T_(L slash K) (x y), quad x, y in L.
$ <eq:trace-form>
Then $tau$ is a symmetric $K$-bilinear form. The form $tau$ is called
_nondegenerate_ if for nonzero $x in L$, the map $tau(x, dot): L -> K$ is not
the zero map. We may represent $tau$ by a symmetric matrix $bolditalic(tau)$ as
follows: let $L = dsum_(i=1)^n K x_i$, where $n = (L : K)$, and put
#idx("nondegenerate form")
$
  bolditalic(tau) = (tau(x_i, x_j))_(1 <= i, j <= n)
  = (T_(L slash K) (x_i x_j))_(1 <= i, j <= n).
$
Then $tau$ is nondegenerate if and only if the matrix $bolditalic(tau)$ is
nonsingular. A standard result in field theory is as follows:

#theorem[
  Let $L$ be a finite field extension of $K$. The following statements are
  equivalent:
  + $L$ is separable over $K$.
  + The bilinear trace form from $L times L$ to $K$ is nondegenerate.
  + There exists an $x in L$ such that $T_(L slash K) (x) = 1$.
  + $T_(L slash K): L -> K$ is an epimorphism.
] <th:separable-trace-form>

(We remind the reader that if $op("char") K = 0$, or more generally if
$op("char") K$ does not divide the degree $(L : K)$, then $L$ is necessarily
separable over $K$. The same is true whenever $K$ is a finite field.)

We give an addendum to @th:integral-closure-dedekind for the case of separable
extensions.

#theorem[
  Let $R$ be a Dedekind domain with quotient field $K$, and let $S$ be #source(
    56,
  )the integral closure of $R$ in a finite separable field extension $L$ of $K$.
  Then $S$ is a finitely generated torsionfree $R$-module of $R$-rank $(L : K)$.
] <th:integral-closure-finitely-generated>

We turn now to the ideal theory of a Dedekind domain $R$. A _fractional
$R$-ideal_ is a full $R$-lattice in $K$, that is, a finitely generated
$R$-submodule $J$ contained in $K$, such that $K dot J = K$. Since $R$ is
noetherian, every nonzero ideal of $R$ is necessarily a fractional ideal, and
will be called an _integral_ ideal. #idx("fractional ideal")#idx(
  "integral ideal",
)#idx("ideal", "fractional")#idx("ideal", "integral")

Given fractional $R$-ideals $J$ and $J'$, we may define
$
    J + J' & = {x + y : x in J, y in J'}, \
  J dot J' & = {sum_"finite" x_i y_i : x_i in J, y_i in J'}, \
    J^(-1) & = {x in K : x J subset R}.
$
Then $J + J'$, $J inter J'$, $J dot J'$ and $J^(-1)$ are fractional $R$-ideals
as well. Relative to the multiplication $J dot J'$ defined above, the set of
fractional $R$-ideals forms a multiplicative group with identity element $R$,
and with $J^(-1)$ the inverse of $J$.

Property @def:dedekind-factorization of Dedekind domains extends readily to the
factorization of fractional ideals, as follows:

#theorem[
  The set of fractional $R$-ideals in $K$ is a free abelian group, with free
  generators the nonzero prime ideals of $R$. In other words, every fractional
  ideal is uniquely expressible in the form
  $
    J = P_1^(e_1) dots P_t^(e_t), quad e_i in bold(Z),
  $
  where the ${P_i}$ are distinct nonzero prime ideals of $R$, and where no $e_i$
  is 0. (We agree to write $R$ itself as an "empty product", with $t = 0$).
] <th:fractional-ideals-free>

Consider next the factorization $J = product P_i^(a_i)$,
$J' = product P_i^(b_i)$, of a pair of fractional ideals. If $a_i <= b_i$ for
each $i$, we say that $J$ _divides_ $J'$ (notation: $J | J'$), and in this case
it is clear that $J supset J'$. Conversely, if $J supset J'$ then
$J^(-1) J' subset R$, whence by @th:fractional-ideals-free $a_i <= b_i$ for each
$i$.

Given any pair of fractional ideals $J$, $J'$, we call $J + J'$ their _greatest
common divisor_, and $J inter J'$ their _least common multiple_. If the
factorizations of $J$ and $J'$ are as above, it follows at once from the
preceding paragraph that #idx("greatest common divisor")#idx(
  "least common multiple",
)
$
  J + J' = product P_i^(min(a_i, b_i)), quad
  J inter J' = product P_i^(max(a_i, b_i)).
$ <eq:gcd-lcm>
Two ideals $J$, $J'$ of $R$ are _relatively prime_ if $J + J' = R$. By
@eq:gcd-lcm, if $J$ and $J'$ are nonzero, they are relatively prime if and only
if they have no prime ideal factor in common. A set of nonzero integral ideals
${J_1, dots, J_n}$ is _pairwise relatively prime_ if $J_i + J_k = R$ for
$1 <= i < k <= n$.
#idx("relatively prime (ideals)")

#theorem(title: [Chinese Remainder Theorem])[
  Let ${J_1, dots, J_n}$ be a set of pairwise relatively prime integral ideals
  of $R$. Then there is a ring isomorphism
  #source(57)
  $
    R slash J_1 dots.c J_n tilde.equiv
    (R slash J_1) dotplus dots.c dotplus (R slash J_n).
  $
  #idx("Chinese remainder theorem", target: [@th:chinese-remainder])
] <th:chinese-remainder>

An easy consequence of @th:chinese-remainder is the extremely important

#theorem(title: [Strong Approximation Theorem])[
  Let $P_1, dots, P_n$ be distinct nonzero prime ideals of the Dedekind domain
  $R$, and let the elements $a_1, dots, a_n in K$ be given, as well as positive
  integers $r_1, dots, r_n$. Then there exists an element $b in K$ such that
  $
    cases(
      b - a_i in (P_i)^(r_i) dot R_(P_i)"," quad 1 <= i <= n",",
      b in R_P quad "for all" P != P_1"," dots"," P_n",",
    )
  $
  where $P$ denotes a variable nonzero prime ideal of $R$.
  #idx("Strong Approximation Theorem", target: [@th:strong-approximation])
] <th:strong-approximation>

We shall also record

#theorem[
  Let $J$ be an integral ideal of the Dedekind domain $R$, and $A$ any
  fractional $R$-ideal. Then there is an $R$-isomorphism
  $
    R slash J tilde.equiv A slash J A.
  $
] <th:residue-of-fractional-ideal>

We may partition the set of fractional ideals of $R$ into _ideal classes_,
putting $J$ and $J'$ into the same class whenever $J tilde.equiv J'$ as
$R$-modules. Note that $J tilde.equiv J'$ if and only if $J' = J x$ for some
$x in K$. The ideal classes form a multiplicative group, the _ideal class group_
of $R$, hereafter denoted by $Cl R$. Multiplication of ideal classes is given by
$[J][J'] = [J dot J']$, where $[J]$ is the class containing $J$. A basic result
tells us that $Cl R$ is a finite group whenever $R = algint {K}$, $K$ an
algebraic number field. (This is a special case of the Jordan–Zassenhaus
@th:jordan-zassenhaus[Theorem]). #idx("ideal", "class")#idx(
  "ideal",
  "class group",
)

Next we recall some properties of $R$-lattices. Let $M$ be an $R$-lattice of
$R$-rank $n$, and set $V = K dot M$, an $n$-dimensional vector space over $K$.
We may write $V = dsum_(i=1)^n K v_i$, and set $N = sum R v_i$, a free full
$R$-lattice in $V$. Since $M$ and $N$ are full lattices in the same space $V$,
there exists a nonzero $r in R$ such that $r dot M subset N$. But
$M tilde.equiv r dot M$, and thus we conclude that $M$ may be embedded in a free
$R$-lattice on $n$ generators. This argument holds for any domain $R$. If
however $R$ is a Dedekind domain, then by @def:dedekind-hereditary $R$ is
hereditary. Hence $M$ is $R$-projective by @th:hereditary-submodules-of-free,
and there is an $R$-isomorphism
$
  M tilde.equiv J_1 dotplus dots.c dotplus J_n,
$
where the ${J_i}$ are fractional $R$-ideals. There must be $n$ summands because
$rank_R M = n$. To complete the discussion of the structure of lattices over a
Dedekind domain, it is necessary to know under what conditions two such external
direct sums of fractional ideals are isomorphic. The complete answer is given by
a theorem of Steinitz:

#source(58)
#theorem[
  Let $R$ be a Dedekind domain. Each $R$-lattice $M$ is $R$-projective, and is
  isomorphic to an external direct sum
  $
    M tilde.equiv J_1 dotplus dots.c dotplus J_n,
  $
  where the ${J_i}$ are fractional $R$-ideals, and $n = rank_R M$. Further, two
  such sums $dsum_(i=1)^n J_i$ and $dsum_(i=1)^m J'_i$ are $R$-isomorphic if and
  only if $m = n$, and the products $J_1 dots.c J_n$, $J'_1 dots.c J'_m$ are in
  the same ideal class.
  #idx("Steinitz's Theorem", target: [@th:steinitz])
] <th:steinitz>

There is a generalization of the invariant factor theorem for modules over
principal ideal rings, as follows:

#theorem(title: [Invariant Factor Theorem])[
  Let $R$ be a Dedekind domain, and let $M$, $N$ be $R$-lattices such that
  $N subset K dot M$. Then there exist elements ${m_i}$ in $M$, and fractional
  $R$-ideals ${J_i}$ and ${E_i}$, such that
  $
    M = J_1 m_1 plus.o dots.c plus.o J_r m_r, quad
    N = E_1 J_1 m_1 plus.o dots.c plus.o E_s J_s m_s,
  $
  where $r = rank_R M$, $s = rank_R N$, and where
  $E_1 supset E_2 supset dots supset E_s$. If $N subset M$, then $R supset E_1$.
  #idx("Invariant Factor Theorem", target: [@th:invariant-factor])
] <th:invariant-factor>

The ideals $E_1, dots, E_s$ occurring above are called the _invariant factors_
of the pair $M$, $N$; they are uniquely determined by the inclusion map
$N subset K dot M$. If $N subset M$ and $K dot N = K dot M$, then $M slash N$ is
an $R$-torsion module, and there is an $R$-isomorphism
$
  M slash N tilde.equiv dsum_(i=1)^r (J_i slash E_i J_i) tilde.equiv
  dsum_(i=1)^r (R slash E_i),
$ <eq:quotient-invariant-factors>
the latter isomorphism being a consequence of @th:residue-of-fractional-ideal.
Then (see below) the order ideal of $M slash N$ is given by
$
  ord M slash N = E_1 dots.c E_r.
$ <eq:order-ideal-invariant-factors>

Let us define the _order ideal_ $ord X$ of a finitely generated $R$-module $X$
as follows:
#idx("order ideal")
+ If $X = 0$, $ord X = R$.
+ If $X$ is not an $R$-torsion module, $ord X = 0$.
+ If $X$ is a nonzero $R$-torsion module, then $X$ has an $R$-composition series
  (see Exercise~@exc:torsion-composition-series), whose composition factors are
  ${R slash P_i}$, with $P_i$ ranging over some set of maximal ideals of $R$. We
  set $ord X = product P_i$, where the number of factors equals the number of
  composition factors of $X$. The ideal $P_i$ can be recovered from the
  composition factor $R slash P_i$, namely
  $
    P_i = ann_R R slash P_i.
  $
Since the set of composition factors is uniquely determined by $X$, according to
the Jordan–Hölder Theorem, it follows that $ord X$ is well-defined.

#source(59)We observe that if $X$ is an $R$-torsion module, then $ord X = R$ if
and only if $X = 0$. Further, we prove

#theorem[
  + For each exact sequence of finitely generated $R$-modules
    $
      0 -> X' -> X -> X'' -> 0,
    $
    we have
    $
      ord X = (ord X')(ord X'').
    $
  + For each nonzero ideal $J$ of $R$, $ord (R slash J) = J$.
] <th:order-ideal-multiplicative>

#proof[
  (i) is clear from the fact that the composition factors of $X$ are those of
  $X'$ together with those of $X''$. For (ii), we can use the factorization
  $J = product P_i^(e_i)$ in @th:fractional-ideals-free to write an explicit
  composition series for $R slash J$, from which it is evident that the
  composition factors of $R slash J$ are the ${R slash P_i}$ with multiplicities
  ${e_i}$.
]

From @th:invariant-factor we obtain a structure theorem for finitely generated
$R$-modules:

#theorem[
  Every finitely generated $R$-module is isomorphic to a finite external direct
  sum of ideals of $R$ and cyclic#footnote[An $R$-module is _cyclic_ if it can
    be generated by one element.] modules $R slash J$, with $J$ an integral
  ideal of $R$.
] <th:finitely-generated-modules-structure>
#idx("cyclic module")

#proof[
  Given a finitely generated $R$-module $X$, we can find an $R$-exact sequence
  $
    0 -> N -> M -> X -> 0,
  $
  with $M$ $R$-free on $r$ generators, $r$ finite. We then have (in the notation
  of @th:invariant-factor)
  $
    X tilde.equiv M slash N tilde.equiv dsum_(i=s+1)^r J_i dotplus
    dsum_(i=1)^s (R slash E_i),
  $
  as claimed. Note that the expression $dsum J_i$ does not occur if $X$ is an
  $R$-torsion module.
]

=== Localizations, valuations <ss:localizations-valuations>

Throughout let $R$ be an integral domain with quotient field $K$, $R != K$. We
shall describe some properties of the ring $R$, and of $R$-modules, with respect
to localization at prime ideals of $R$. In cases where proofs are omitted, the
reader may consult the references listed at the beginning of
§~@sec:dedekind-domains. For the first part of this subsection, we shall
restrict our attention to Dedekind #source(60)domains. In the second part, we
shall consider the more general situation in which $R$ is a noetherian
integrally closed domain. This more general material may be skipped in a first
reading, since it will occur only peripherally in later chapters.

Let us introduce some concepts from valuation theory (we shall consider only
rank one valuations!). Let $bold(R)$ be the real field, $bold(R)^+$ the set of
nonnegative real numbers.

#definition[
  A _valuation_ of $K$ is a mapping $phi: K -> bold(R)^+$ such that for
  $a, b in K$,
  + $phi(a) = 0$ if and only if $a = 0$.
  + $phi(a b) = phi(a) phi(b)$.
  + $phi(a + b) <= phi(a) + phi(b)$.
  If the valuation also satisfies the stronger condition
  #enum(start: 4, [$phi(a + b) <= max(phi(a), phi(b))$,])
  we call $phi$ _non-archimedean_. It is easily verified that every
  non-archimedean valuation satisfies
  #enum(start: 5, [$phi(a + b) = max(phi(a), phi(b))$ whenever
    $phi(a) != phi(b)$.])
  #idx("valuation")#idx("non-archimedean valuation")
] <def:valuation>

The _trivial_ valuation is defined by the formulas $phi(0) = 0$, $phi(a) = 1$
for $a in K$, $a != 0$. We shall always exclude the trivial valuation in our
discussion in §§~@sec:dedekind-domains–@sec:completions-and-valuations, so
hereafter the term "valuation" always means "non-trivial valuation".
#idx("trivial valuation")

The _value group_ of a valuation $phi$ is the multiplicative group
${phi(a) : a in K, a != 0}$. If this value group is an infinite cyclic group,
$phi$ is a _discrete_ valuation, and is necessarily non-archimedean. #idx(
  "value group (of valuation)",
)#idx("discrete valuation")

Two valuations $phi$, $psi$ are _equivalent_ if for $a in K$,
#idx("equivalence", "of valuations")
$
  phi(a) <= 1 quad "if and only if" quad psi(a) <= 1.
$
Each valuation $phi$ on $K$ gives rise to a topology on $K$, by taking as basis
for the neighborhoods of a point $a in K$ the sets
$
  {x in K : phi(x - a) < epsilon},
$
where $epsilon$ ranges over all positive real numbers. Equivalent valuations
give the same topology on $K$.

Given any non-archimedean valuation $phi$ on $K$, let us put
$
  R = {a in K : phi(a) <= 1}.
$
Then $R$ is a ring, and is called the _valuation ring_ of $phi$. The set
#idx("valuation ring")
$
  P = {a in K : phi(a) < 1}
$
is the unique maximal ideal of $R$. If $phi$ is a discrete valuation, then $P$
is a #source(61)principal ideal, namely $P = R pi$ where $pi$ is any element of
$P$ such that $phi(pi) < 1$ and $phi(pi)$ generates the value group of $phi$. In
this case $R$ is a _discrete valuation ring_, by which we shall mean a principal
ideal domain having a unique maximal ideal $P$, and such that $P != 0$.
#idx("discrete valuation ring")

One way of obtaining archimedean valuations is as follows: the ordinary absolute
value $|thin|$ on the complex field $bold(C)$ is an archimedean valuation, whose
restriction to any subfield of $bold(C)$ is an archimedean valuation on that
subfield. Now let $K$ be a field which can be embedded in $bold(C)$, and let
$mu: K -> bold(C)$ be an embedding. Define $phi: K -> bold(R)^+$ by setting
#idx("archimedean valuation")
$
  phi(a) = |mu(a)|, quad a in K.
$
Then $phi$ is an archimedean valuation on $K$.

In particular, every algebraic number field $K$ can be embedded in $bold(C)$.
For we may write $K = bold(Q)(a)$, and let $f(X) = minpol_bold(Q) (a)$. Then
there exist elements ${alpha_i}$ in $bold(C)$ such that
$f(X) = product (X - alpha_i)$, and we may define embeddings
$mu_i: K -> bold(C)$ by
$
  mu_i {g(a)} = g(alpha_i), quad "for each" quad g(X) in bold(Q)[X].
$
If $f(X)$ has $r_1$ real zeros $alpha_1, dots, alpha_(r_1)$ and $2 r_2$ nonreal
zeros in $bold(C)$, arranged in pairs of complex conjugates
$alpha_(r_1 + 1), overline(alpha)_(r_1 + 1), dots, alpha_(r_1 + r_2),
overline(alpha)_(r_1 + r_2)$, then there are exactly $r_1 + r_2$ inequivalent
archimedean valuations of $K$. These are given by the above construction, using
the $r_1 + r_2$ embeddings $K -> bold(C)$ defined by letting $a -> alpha_i$,
$1 <= i <= r_1 + r_2$. (The embedding in which $a -> overline(alpha)_i$ is
equivalent to that where $a -> alpha_i$, for $r_1 + 1 <= i <= r_1 + r_2$.)

The non-archimedean valuations of algebraic number fields can be described in a
similar way, by means of embeddings into $P$-adic fields, which are fields
complete with respect to certain non-archimedean valuations. We shall say more
about this point of view in §~@sec:completions-and-valuations. In the present
subsection, we shall instead give the connection between prime ideals of
Dedekind domains and non-archimedean valuations.

Assume now that $R$ is a Dedekind domain, and let $P$ be a nonzero prime ideal
of $R$, or equivalently, a maximal ideal of $R$. For each nonzero $a in K$, we
may factor the principal ideal $R a$ into a product of powers of prime ideals,
as in @th:fractional-ideals-free. Let $v_P (a)$ denote the exponent to which $P$
occurs in this factorization. If $P$ does not occur, set $v_P (a) = 0$. Also, we
put $v_P (0) = +infinity$. Now fix some $kappa in bold(R)^+$, $kappa > 1$, and
define
$
  phi_P (a) = kappa^(-v_P (a)), quad a in K, quad a != 0,
$
and $phi_P (0) = 0$. Then $phi_P$ is a discrete non-archimedean valuation on
$K$, whose value group is the cyclic group generated by $kappa$. (If instead of
$kappa$ we used another real number $kappa'$, with $kappa' > 1$, the valuation
$phi'_P$ thus obtained would be equivalent to the above-defined valuation
$phi_P$.)

#source(62)We refer to $v_P$ as the _exponential valuation_ associated with $P$.
The properties of $phi_P$ listed in @def:valuation are consequences of the
following properties of $v_P$: #idx("exponential valuation")#idx(
  "valuation (exponential)",
)

#condition(variant: [@def:valuation], suffix: "a")[
  For any elements $a, b in K$, we have
  + $v_P (a) = infinity$ if and only if $a = 0$.
  + $v_P (a b) = v_P (a) + v_P (b)$.
  + $v_P (a + b) >= min(v_P (a), v_P (b))$, with equality whenever
    $v_P (a) != v_P (b)$.
] <def:exponential-valuation>

As in §~@ss:localization-at-prime-ideals, we shall denote by $R_P$ the
_localization_ of $R$ at $P$, defined by
$
  R_P = {x slash s : x in R, s in R - P}.
$
This ring is in fact the valuation ring of the $P$-adic valuation $phi_P$ on
$K$, and its unique maximal ideal is precisely $P dot R_P$. Thus $R_P$ is a
discrete valuation ring, and is automatically a principal ideal domain. We may
choose a _prime element_ $pi$ of the ring $R_P$, that is, an element $pi in R_P$
such that $pi R_P = P dot R_P$. Indeed, $pi$ may be chosen to lie in $R$. The
fractional $R_P$-ideals of $K$ are ${pi^n R_P : n in bold(Z)}$. It follows from
@th:localization-residue-modules that localization does not affect residue class
fields, that is,
#idx("prime element")
$
  R slash P tilde.equiv R_P slash P dot R_P.
$
This isomorphism is not only an $R$-isomorphism as asserted in
@th:localization-residue-modules, but is in fact an isomorphism of fields. More
generally, there are ring isomorphisms
$
  R slash P^n tilde.equiv R_P slash P^n dot R_P, quad n >= 1.
$

Keeping the above notation, let $J$ be any fractional $R$-ideal in $K$. Let
$v_P (J)$ denote the exponent to which $P$ occurs in the factorization of $J$
into a product of powers of prime ideals.

#theorem[
  Let $P$ be a maximal ideal of the Dedekind domain $R$.
  + For each fractional $R$-ideal $J$ of $K$, the localization $J_P$ is given by
    $
      J_P = (P dot R_P)^(v_P (J)).
    $
  + For any finitely generated $R$-module $X$,
    $
      (ord X)_P = ord (X_P).
    $
  + For any finitely generated $R$-module $M$, we have $M_P = 0$ if and only if
    $P + ann_R M = R$.
] <th:localization-dedekind>

#proof[
  Statement (i) is well known (see references), and can easily be deduced from
  the formula
  $
    v_P (J) = min {v_P (a) : a in J}.
  $
  As a consequence of (i), we have $R_P = J_P$ for each integral ideal $J$ of
  $R$ relatively prime to $P$.

  #source(63)Statement (ii) follows from the preceding remarks. First of all,
  unless $X$ is an $R$-torsion module, both $ord X$ and $ord X_P$ are 0. Next,
  if $X$ is a nonzero $R$-torsion module, it has a composition series
  $
    X supset X' supset X'' supset dots.c supset X^((k)) supset 0,
  $
  whose composition factors are (say) $R slash P_1, R slash P_2, dots,
  R slash P_k$, with the ${P_i}$ maximal ideals of $R$. Then
  $
    X_P supset (X')_P supset dots.c supset (X^((k)))_P supset 0
  $
  is a descending chain of $R$-modules, possibly with repetitions, and with
  factor modules ${(R slash P_i)_P}$. But
  $
    (R slash P_i)_P tilde.equiv R_P slash (P_i)_P tilde.equiv
    cases(0"," & P_i != P",", R slash P"," & P_i = P.)
  $
  Therefore
  $
    ord X_P = product_(P_i = P) (P_i)_P = (product_(P_i = P) P_i)_P
    = (ord X)_P,
  $
  as claimed. (See also Exercise~@exc:order-ideal-extension).

  Finally we prove (iii), remarking in advance that the proof will be valid for
  the more general case where $R$ is any commutative ring, and $P$ a maximal
  ideal of $R$. Let $S = R - P$, a multiplicative subset of $R$. By definition,
  $M_P = S^(-1) M$; thus $M_P = 0$ if and only if $M$ is an $S$-torsion module.
  Since $M$ is finitely generated as $R$-module, we see that $M$ is an
  $S$-torsion module if and only if there exists an $s in S$ such that
  $s dot M = 0$. But this occurs if and only if $ann_R M subset.not P$, that is,
  if and only if $P + ann_R M = R$. This completes the proof.
]

So far we have considered only localizations at a single maximal ideal $P$ of
$R$. In order to study relationships between "local" and "global" questions, one
often needs results of the following type, in which the entire set of
localizations are considered simultaneously.

#theorem[
  Let $R$ be a Dedekind ring with quotient field $K$, and let $M$ be any
  $R$-lattice. View $M$ and its localizations ${M_P}$ as embedded in the vector
  space $K M$ over $K$. Then
  $
    M = inter.big_P M_P,
  $
  the intersection being formed within $K M$, and where $P$ ranges over all
  maximal ideals of $R$.
] <th:lattice-intersection-of-localizations>

#proof[
  By @th:steinitz, the $R$-lattice $M$ is $R$-projective. The desired assertion
  is now a consequence of Exercise~@exc:module-intersection-of-localizations.
]

In the same vein, we prove

#source(64)
#theorem(major: true)[
  Let $R$ be a Dedekind domain, $M$ an $R$-lattice, and let $V = K M$. For each
  maximal ideal $P$ of $R$, let there be given a full $R_P$-lattice $X(P)$ in
  $V$, such that $X(P) = M_P$ a.e.#footnote["a.e." means "almost everywhere",
    that is, for all but a finite number of $P$'s.] <fn:ae>
  Define
  $
    N = inter.big_P X(P),
  $
  the intersection being formed within $V$. Then $N$ is a full $R$-lattice in
  $V$, and
  $
    N_P = X(P) quad "for all" P.
  $
] <th:lattice-from-local-data>
#idx("a.e. (almost everywhere)")

#proof[
  Let $V = dsum_(i=1)^r K v_i$, and set $L = dsum_(i=1)^r R v_i$. Then $L$ is a
  full $R$-lattice in $V$, and so $L_P = M_P$ a.e.#footnote(<fn:ae>) (See
  Exercise~@exc:full-lattices-equal-ae). Therefore $L_P = X(P)$ a.e., and so we
  may choose nonzero $a, b in R$ such that
  $
    a dot X(P) subset L_P subset b dot X(P)
  $
  for all $P$. Then
  $
    N = inter.big X(P) subset a^(-1) inter.big L_P = a^(-1) L,
  $
  so $N$ is an $R$-lattice in $V$. Likewise $L subset b N$, so $N$ is a full
  $R$-lattice in $V$.

  It remains for us to show that $N_P = X(P)$ for each $P$. Since
  $N subset X(P)$, it follows that
  $
    N_P subset R_P dot X(P) = X(P).
  $
  To prove the reverse inclusion, let us first write
  $N = R n_1 + dots.c + R n_s$, where of course $s >= r$. Then each $x in X(P)$
  is expressible as a sum $x = sum_(i=1)^s a_i n_i$, $a_i in K$. By the Strong
  Approximation Theorem @th:strong-approximation, we may find elements
  $b_1, dots, b_s in K$ such that
  $
    b_i - a_i in R_P, quad b_i in R_(P') thin (P' != P), quad 1 <= i <= s,
  $
  where $P'$ ranges over all maximal ideals of $R$ distinct from $P$. Let us put
  $y = sum b_i n_i$. Then for $P' != P$, we have
  $y in R_(P') dot N subset X(P')$; on the other hand,
  $y - x = sum (b_i - a_i) n_i in R_P dot N subset N_P$, so also $y in X(P)$.
  Therefore $y in N$, and so
  $
    x = y - (y - x) in N_P.
  $
  This shows that $X(P) subset N_P$, and completes the proof.
]

Let $M$ be an $R$-module, where $R$ is any domain, and define the $R$-modules
$
  M^* = Hom_R (M, R), quad M^(**) = Hom_R (M^*, R).
$ <eq:dual-module>
The _evaluation map_ $phi: M -> M^(**)$ is given by
#idx("evaluation map")
$
  {phi(m)} f = f(m), quad f in M^*.
$
Clearly $phi = 0$ if and only if $M^* = 0$. We call $M$ _reflexive_ if $phi$ is
an isomorphism.
#idx("reflexive")

#source(65)
#theorem[
  Let $R$ be a Dedekind domain. Then every $R$-lattice is reflexive, that is,
  $M tilde.equiv M^(**)$.
] <th:lattices-reflexive>

#proof[
  By @th:steinitz each $R$-lattice $M$ is isomorphic to an external direct sum
  of fractional $R$-ideals $J$ of $K$. Since the functors involved in
  @eq:dual-module commute with finite direct sums, it suffices to prove the
  theorem for the case where $M = J$. Now $J^* = Hom_R (J, R)$, and each
  $f in J^*$ extends to a map $f' in Hom_K (K, K)$. Each such $f'$ is given by a
  right multiplication by an element $a in K$, and so there is an identification
  $
    J^* = {a in K : J dot a subset R}.
  $
  Therefore $J^* = J^(-1)$, and so $J^(**) = (J^(-1))^(-1) = J$. Thus the result
  holds for $M = J$, and hence also for every $R$-lattice $M$. (See also
  Exercise~@exc:reflexive-projective.)
]

Combining the results of @th:lattices-reflexive and
@th:lattice-intersection-of-localizations, we find that
$
  M^(**) = inter.big_P M_P
$
for any lattice $M$ over a Dedekind domain $R$. An analogous result holds under
somewhat more general circumstances, described below. Let $R$ be any domain; a
_minimal prime_ of $R$ is a nonzero prime ideal of $R$ which is minimal among
the set of all nonzero prime ideals of $R$.
#idx("minimal prime")

Let $M$ be an $R$-lattice, where $R$ is a noetherian domain, and let $V = K M$.
Then define dual spaces
$
  V^* = Hom_K (V, K), quad V^(**) = Hom_K (V^*, K).
$
The evaluation map gives a $K$-isomorphism $V tilde.equiv V^(**)$. Since $R$ is
noetherian, $M^*$ and $M^(**)$ are also $R$-lattices, and there are embeddings
$M^* subset V^*$, $M^(**) subset V^(**)$. Explicitly we have
$
  M^(**) = {v in V : f(v) in R quad "for all" f in M^*}.
$

#theorem[
  Let $R$ be a noetherian integrally closed domain, $M$ an $R$-lattice, and let
  $P$ range over the minimal primes of $R$. Then
  + For each $P$, $R_P$ is a discrete valuation ring (that is, a principal ideal
    domain with unique maximal ideal $P dot R_P$).
  + $R = inter.big_P R_P$.
  + For each nonzero $x in R$, $x$ is a unit in $R_P$ a.e.
  + $M^(**) = inter.big_P M_P$.
] <th:krull-ring>

#remark(kind: "Remarks", numbered: false)[
  The proof of (i) may be found in Serre [@bib:Serre1962, p.~19, Prop.~3]. As
  general reference, see Bourbaki [@bib:Bourbaki1965], Fossum
  [@bib:Fossum1973a].

  Conditions (i)–(iii) are the postulates for a _Krull ring_. Thus the theorem
  asserts that every noetherian integrally closed domain is a Krull ring. The
  #idx("Krull ring")
  #source(66)converse is false: Krull rings are always integrally closed, but
  need not be noetherian. For example $bold(Z)[X_1, X_2, dots]$ is a
  non-noetherian Krull ring. Every unique factorization domain is automatically
  a Krull ring. As examples of noetherian integrally closed domains, we list
  $bold(Z)[X_1, dots, X_n]$ and $K[X_1, dots, X_n]$.
]

The following generalization of @th:lattice-from-local-data is proved in the
above-named references (see, for instance, Bourbaki [@bib:Bourbaki1965, Ch.~7,
§~4, No.~3]):

#theorem[
  Let $R$ be a noetherian integrally closed domain, and let $M$ and $L$ be full
  $R$-lattices in the $K$-space $V$. Let $P$ range over the minimal primes of
  $R$. Then $M_P = L_P$ a.e. Further, let there be given for each $P$ a full
  $R_P$-lattice $X(P)$ in $V$, such that $X(P) = M_P$ a.e. Set
  $
    N = inter.big_P X(P).
  $
  Then $N$ is a full reflexive $R$-lattice in $V$, and $N_P = X(P)$ for all $P$.
] <th:krull-lattice-from-local-data>

#heading(level: 3)[Ramification index; residue class degree]
<ss:ramification-index-residue-degree>

Throughout this section, $R$ is a Dedekind domain with quotient field $K$, and
$L$ is a finite separable field extension of $K$. We shall denote by $S$ the
integral closure of $R$ in $L$, so by @th:integral-closure-dedekind and
@th:integral-closure-finitely-generated, $S$ is a Dedekind domain with quotient
field $L$, finitely generated as $R$-module, of $R$-rank $(L : K)$. To avoid
trivialities, we assume always that $R != K$ and $L != S$.

Given a maximal ideal $P$ of $R$, the integral ideal $P dot S$ can be written as
$
  P dot S = product_(i=1)^g P_i^(e_i),
$ <eq:prime-decomposition>
where the ${P_i}$ are distinct maximal ideals of $S$, and the ${e_i}$ are
positive integers. Call $e_i$ the _ramification index_ of $P_i$ for the
extension $L slash K$, and write
#idx("ramification index")
$
  e_i = e(P_i, L slash K), quad 1 <= i <= g.
$ <eq:ramification-index>
We say that $P_i$ is _unramified_ in $L slash K$ if $e_i = 1$ and $S slash P_i$
is a separable extension of $R slash P$. Likewise, we say that $P$ is
_unramified_ in the extension $L slash K$ if each $P_i$ is unramified in
$L slash K$.
#idx("unramified")

Turning to residue class fields, we observe at once that for $1 <= i <= g$, the
field $S slash P_i$ is an extension field of $R slash P$. We set
$
  f_i = f(P_i, L slash K) = (S slash P_i : R slash P),
$ <eq:residue-degree>
and call $f_i$ the _residue class degree_ of $P_i$ relative to the extension
$L slash K$. The finiteness of the ${f_i}$ is a consequence of the following
basic result:
#idx("residue class degree")

#source(67)
#theorem[
  Keeping the above notation, we have
  $
    sum_(i=1)^g e_i f_i = (L : K).
  $
] <th:sum-ef>

#proof[
  Let $n = (L : K)$, so $rank_R S = n$. Let $S_P = R_P dot S$; then $S_P$ is a
  torsionfree $R_P$-module of $R_P$-rank $n$. But $R_P$ is a principal ideal
  domain, and so $S_P tilde.equiv R_P^((n))$. Therefore
  $
    S slash P S tilde.equiv S_P slash P dot S_P tilde.equiv
    (R_P slash P dot R_P)^((n)) tilde.equiv (R slash P)^((n))
  $
  by virtue of @eq:residue-module-local. This shows that the dimension of
  $S slash P S$ as vector space over the field $R slash P$ is precisely $n$.

  We may also compute this dimension as follows: by @th:chinese-remainder we
  have
  $
    S slash P S = S slash product P_i^(e_i) tilde.equiv
    dsum_(i=1)^g (S slash P_i^(e_i)).
  $
  There is a descending chain of $R slash P$-modules
  $
    S slash P_i^(e_i) supset P_i slash P_i^(e_i) supset dots.c supset
    P_i^(e_i - 1) slash P_i^(e_i) supset 0,
  $
  each of whose factor modules is isomorphic to $S slash P_i$ by
  @th:residue-of-fractional-ideal. Hence
  $
    dim_(R slash P) (S slash P_i^(e_i)) = e_i dot dim_(R slash P) (S slash P_i)
    = e_i f_i,
  $
  for each $i$, $1 <= i <= g$. This gives
  $
    dim_(R slash P) (S slash P S) = sum_(i=1)^g e_i f_i,
  $
  and the theorem is proved.
]

#remark(kind: "Comments")[
  + It is easily verified that $S_P$ is the integral closure of $R_P$ in $L$,
    and that ${P_i dot S_P : 1 <= i <= g}$ are the distinct maximal ideals of
    $S_P$. Furthermore,
    $
      S_P = S_(P_1) inter dots.c inter S_(P_g),
    $
    where $S_(P_i)$ is the localization of $S$ at $P_i$, and where
    $S_P = R_P dot S$. Note that $R_P$ is a discrete valuation ring, but $S_P$
    is not (unless $g = 1$). In connection with this remark, see
    Exercise~@exc:semilocal-ring.
  + If @eq:prime-decomposition holds, then we claim that $P_i inter R = P$,
    $1 <= i <= g$. Indeed, $P_i inter R$ is a prime ideal of $R$ containing $P$,
    or else possibly $P_i inter R = R$. The latter alternative cannot occur,
    since $1 in.not P_i$.

    On the other hand, starting with any maximal ideal $P_i$ of $S$, we may set
    $P = P_i inter R$, a prime ideal of $R$. Surely $P != 0$, since for each
    nonzero $a in P_i$, the constant term in $minpol_K (a)$ is a nonzero element
    in $P$. Thus $P_i supset P$, #source(68)and so $P_i supset P dot S$, whence
    $P_i$ occurs in the factorization of $P dot S$ into maximal ideals of $S$.
  + We may define a _relative norm map_ $N_(L slash K)$ which associates to each
    fractional $S$-ideal $J$ of $L$, a fractional $R$-ideal $N_(L slash K) (J)$
    of $K$. For each maximal ideal $P_i$ of $S$, we set #idx(
      "relative norm",
    )#idx("norm (of ideal)")
    $
      N_(L slash K) (P_i) = P^(f_i), "where" P = P_i inter R, quad
      f_i = f(P_i, L slash K).
    $ <eq:relative-norm-prime>
    Since these ${P_i}$ form a free basis for the abelian group of fractional
    $S$-ideals in $L$, we may then define $N_(L slash K)$ on this group by
    requiring it to be multiplicative:
    $
      N_(L slash K) (J J') = N_(L slash K) (J) dot N_(L slash K) (J').
    $

    We could also have defined the norm map $N_(L slash K)$ as follows: for each
    nonzero ideal $J$ of $S$, put
    $
      tilde(N)_(L slash K) (J) = ord_R (S slash J),
    $
    where $ord_R$ denotes $R$-order ideal (see §~@ss:ideal-theory-modules). If
    $J'$ is another nonzero ideal of $S$, there is an $R$-exact sequence
    $
      0 -> J slash J J' -> S slash J J' -> S slash J -> 0,
    $
    and by @th:residue-of-fractional-ideal the term $J slash J J'$ is isomorphic
    to $S slash J'$. From @th:order-ideal-multiplicative we then conclude
    $
      ord_R (S slash J J') = ord_R (S slash J) dot ord_R (S slash J'), quad
      "that is," quad tilde(N)(J J') = tilde(N)(J) dot tilde(N)(J').
    $
    If we now put
    $
      tilde(N)_(L slash K) (J_1 dot J_2^(-1))
      = tilde(N)_(L slash K) (J_1) dot tilde(N)_(L slash K) (J_2)^(-1)
    $
    for $J_1$, $J_2$ nonzero ideals of $S$, it follows that
    $tilde(N)_(L slash K)$ is well defined on the group of fractional $S$-ideals
    in $L$. We now show that $tilde(N)_(L slash K)$ coincides with
    $N_(L slash K)$. It suffices to verify that
    $
      ord_R (S slash P_i) = P^(f_i),
    $ <eq:norm-order-ideal>
    using the notation of @eq:relative-norm-prime. But $S slash P_i$ is a field
    extension of $R slash P$ of degree $f_i$, so as $R$-modules we have
    $S slash P_i tilde.equiv (R slash P)^((f_i))$, and then @eq:norm-order-ideal
    is obvious.
  + In the special case where $K = bold(Q)$, $R = bold(Z)$, one defines a
    _counting norm_ $cal(N)_(L slash bold(Q))$, by setting #idx(
      "counting norm",
    )#idx("norm (counting)")
    $
      cal(N)_(L slash bold(Q)) (P_i) = p^(f_i), quad
      f_i = f(P_i, L slash bold(Q)),
    $
    where $p$ is the positive rational prime such that
    $p bold(Z) = P_i inter bold(Z)$. Thus $cal(N)_(L slash bold(Q)) (P_i)$ is
    the number of elements in the finite field $S slash P_i$. As usual,
    $cal(N)_(L slash bold(Q))$ is defined on all fractional $S$-ideals in $L$,
    so as to be multiplicative. Then for each nonzero ideal $J$ in $S$,
    #source(69)
    $
      cal(N)_(L slash bold(Q)) (J) = card (S slash J),
    $
    where $card (S slash J)$ denotes the number of elements in the ring
    $S slash J$.
  + If $L$ is a galois extension of $K$, with galois group $G$, then for each
    $sigma in G$ we have $S^sigma = S$, where $S^sigma = {x^sigma : x in S}$. It
    is well known (see references) that $G$ acts transitively on the set of
    prime ideals ${P_i}$ occurring in @eq:prime-decomposition, that is, there
    exist elements ${sigma_i} in G$ such that $P_i = (P_1)^(sigma_i)$,
    $1 <= i <= g$. Furthermore, in this case we have
    $
      e_1 = dots.c = e_g, quad f_1 = dots.c = f_g.
    $
] <rem:ramification-comments>

=== Different, discriminant <ss:different-discriminant>

As in §~@ss:ramification-index-residue-degree, let $L$ be a finite separable
field extension of $K$, let $R$ be a Dedekind domain with quotient field $K$,
and let $S$ be the integral closure of $R$ in $L$. Let $tau: L times L -> K$ be
the nondegenerate bilinear trace form defined in @eq:trace-form, that is,
$
  tau(x, y) = T_(L slash K) (x y), quad x, y in L.
$
For any set $J subset L$, put
$
  tau(x, J) = T_(L slash K) (x J) = {tau(x, y) : y in J}.
$
We prove at once that $T_(L slash K) (S) subset R$. Indeed, each $a in S$ is
integral over $R$, so $charpol_(L slash K) a in R[X]$ by
Exercise~@exc:char-pol-integral. Therefore $T_(L slash K) a in R$, as desired.

Given any full $R$-lattice $M$ in $L$, we can define a _complementary_ lattice
#idx("complementary lattice")
$
  tilde(M) = {x in L : tau(x, M) subset R}.
$
The map $M -> tilde(M)$ is inclusion-reversing. Let us verify that $tilde(M)$ is
a full $R$-lattice in $L$. First observe that $M$ is contained in some full free
$R$-lattice $N = dsum_(i=1)^n R x_i$, where $n = (L : K)$. There exist elements
${y_j} in L$ such that $tau(x_i, y_j) = delta_(i j)$, $1 <= i, j <= n$. Then
$
  tilde(M) supset tilde(N) = dsum_(j=1)^n R y_j.
$
Similarly, $tilde(M)$ is contained in some full $R$-lattice in $L$. Therefore
$tilde(M)$ is itself a full $R$-lattice in $L$, as claimed.

In particular, if $J$ is a fractional $S$-ideal in $L$, then $tilde(J)$ is an
$S$-submodule of $L$ which is an $R$-lattice, and thus $tilde(J)$ is also a
fractional $S$-ideal of $L$; we call $tilde(J)$ the _complementary ideal_ of
$J$. For the case where $J$ is $S$ itself, we note that $tilde(S) supset S$, so
that $tilde(S)^(-1)$ is an integral ideal of $S$. Let us define the _different_
of $S$ with respect to $R$ as #idx("complementary ideal")#idx("different")
$
  frak(D)(S slash R) = tilde(S)^(-1),
$
and then $tilde(S) = frak(D)(S slash R)^(-1)$ may be referred to as the _inverse
different_.
#idx("inverse different")

#source(70)
#theorem[
  Let $J$ be a fractional $S$-ideal in $L$. Then
  $
    tilde(J) = J^(-1) dot frak(D)(S slash R)^(-1), quad tilde(tilde(J)) = J.
  $
] <th:complementary-ideal>

#proof[
  Let us abbreviate $T_(L slash K)$ as $T$, and $frak(D)(S slash R)$ as
  $frak(D)$. We have
  $
    T(J dot J^(-1) frak(D)^(-1)) = T(S dot frak(D)^(-1)) subset R,
  $
  so $tilde(J) supset J^(-1) frak(D)^(-1)$. On the other hand,
  $
    R supset T(J tilde(J)) = T(J tilde(J) dot S),
  $
  whence $J tilde(J) subset frak(D)^(-1)$, so
  $tilde(J) subset J^(-1) frak(D)^(-1)$. This proves that
  $tilde(J) = J^(-1) dot frak(D)^(-1)$. The formula for $tilde(tilde(J))$ is
  then obvious (see also Exercise~@exc:dual-lattice-form).
]

The _discriminant_ of $S$ with respect to $R$ is defined as
$
  d(S slash R) = N_(L slash K) (frak(D)(S slash R)),
$
the norm of the different $frak(D)(S slash R)$. Thus $d(S slash R)$ is a nonzero
ideal of $R$, often called the _discriminant ideal_ of $S slash R$.
#idx("discriminant (ideal)")

#theorem[
  + For each maximal ideal $P$ of $R$,
    $
      {d(S slash R)}_P = d(S_P slash R_P).
    $
  + If
    $
      S = dsum_(i=1)^n R x_i, quad n = (L : K),
    $
    then
    $
      d(S slash R) = R dot det (T_(L slash K) (x_i x_j))_(1 <= i, j <= n).
    $
] <th:discriminant-local-and-basis>

#proof[
  For $P$ a maximal ideal of $R$, and $J$ any $S$-ideal in $L$, we put
  $J_P = R_P dot J$, an $S_P$-ideal of $L$. As remarked earlier, $S_P$ is the
  integral closure of $R_P$ in $L$, so in the passage from the pair $R$, $S$ to
  the pair $R_P$, $S_P$, we have introduced a new pair of Dedekind domains, with
  quotient fields $K$, $L$, respectively. The advantage of this procedure is
  that the new domain $R_P$ is a principal ideal domain, and thus $S_P$ is
  $R_P$-free on $n$ generators, where $n = (L : K)$.

  Since the trace map $T_(L slash K)$ is $K$-linear, it follows easily that
  $
    frak(D)(S_P slash R_P) = {frak(D)(S slash R)}_P.
  $ <eq:different-local>
  Furthermore, for each $S$-ideal $J$ in $L$, we have
  $
    N_(L slash K) (J_P) = {N_(L slash K) (J)}_P,
  $
  that is, forming norms commutes with localization. Applying $N_(L slash K)$ to
  @eq:different-local yields assertion (i) of the theorem.

  #source(71)Now suppose that $S$ happens to be $R$-free, say
  $S = dsum_(i=1)^n R x_i$. There exist elements ${y_j} in L$ with
  $T_(L slash K) (x_i y_j) = delta_(i j)$, $1 <= i, j <= n$. Then
  $
    frak(D)(S slash R) = tilde(S)^(-1), "where" tilde(S) = dsum_(j=1)^n R y_j.
  $
  We have
  $
    d(S slash R) & = N_(L slash K) (frak(D)(S slash R))
                   = ord_R (S slash frak(D)(S slash R)) \
                 & = ord_R (S slash tilde(S)^(-1)) = ord_R (tilde(S) slash S)
                   quad ("by" #[@th:residue-of-fractional-ideal]).
  $
  Write
  $
    x_i = sum_(j=1)^n a_(i j) y_j, quad a_(i j) in R, quad 1 <= i <= n.
  $
  Then (Exercise~@exc:order-ideal-determinant)
  $
    ord_R (tilde(S) slash S) = R dot det(a_(i j)).
  $
  But $a_(i j) = T_(L slash K) (x_i x_j)$, which completes the proof of (ii).
]

We may remark that this theorem enables us to compute the discriminant
$d(S slash R)$ by calculating each "local" component $d(S slash R)_P$, and that
by (ii), each local component can be obtained once an $R_P$-basis of $S_P$ is
known.

The different $frak(D)(S slash R)$ and the discriminant $d(S slash R)$ are of
great importance because they give information about ramification of prime
ideals in the extension $L slash K$. Recall that a maximal ideal $P_i$ of $S$ is
_unramified_ in $L slash K$ if
$
  e(P_i, L slash K) = 1, "and" S slash P_i "is a separable extension of"
  R slash P.
$
Likewise, a maximal ideal $P$ of $R$ is _unramified_ in $L slash K$ if
$P dot S = product P_i$, a product of distinct unramified prime ideals of $S$.

#theorem[
  A maximal ideal $P_i$ of $S$ is unramified in the extension $L slash K$ if and
  only if $P_i divides.not frak(D)(S slash R)$. A maximal ideal $P$ of $R$ is
  unramified in $L slash K$ if and only if $P divides.not d(S slash R)$.
] <th:unramified-different>

#proof[
  Let $overline(R) = R slash P$, $overline(S) = S slash P S$, $n = (L : K)$;
  then $overline(S)$ is an algebra over the field $overline(R)$, of dimension
  $n$. For $f(X) in R[X]$, let $overline(f)(X)$ denote its image in
  $overline(R)[X]$. We claim that for $a in S$,
  $
    overline(charpol_(L slash K) a) =
    charpol_(overline(S) slash overline(R)) overline(a).
  $ <eq:char-pol-reduction>
  To prove this, first replace $R$ by $R_P$, and $S$ by $S_P$. Such a change
  does not affect $overline(R)$ or $overline(S)$. Then we may write
  $
    S_P = dsum_(i=1)^n R_P x_i, quad
    overline(S) = dsum_(i=1)^n overline(R) overline(x)_i.
  $
  #source(72)For $a in S$, we have
  $
    a x_j = sum alpha_(i j) x_i, quad
    overline(a) overline(x)_j = sum overline(alpha)_(i j) overline(x)_i, quad
    alpha_(i j) in R.
  $
  Then $charpol (a)$ is the characteristic polynomial of the matrix
  $(alpha_(i j))$, while $charpol (overline(a))$ is that of
  $(overline(alpha)_(i j))$, which establishes @eq:char-pol-reduction at once.

  Now let $P_1$ be a maximal ideal of $S$, and let $P dot S = P_1^e J$, where
  $e >= 1$ and where $J$ is an integral ideal of $S$ relatively prime to $P_1$.
  For each $a in P_1 J$ we have $overline(a)^e = 0$ in $overline(S)$, and
  therefore $charpol_(overline(S) slash overline(R)) overline(a) = X^n$. Hence
  from @eq:char-pol-reduction we conclude that $T_(L slash K) (P_1 J) subset P$.
  Writing $frak(D)$ instead of $frak(D)(S slash R)$ for convenience, we then
  obtain $P_1 J subset P frak(D)^(-1)$, and consequently
  $frak(D) subset P_1^(e-1)$. Thus $P_1^(e-1) | frak(D)$, and therefore
  $P_1 | frak(D)$ whenever $e > 1$.

  To complete the proof, we now assume that $e = 1$, and we must show that
  $P_1 | frak(D)$ if and only if $S slash P_1$ is inseparable over
  $overline(R)$. Since $e = 1$, we have
  $
    overline(S) = S slash P S tilde.equiv S slash P_1 dotplus S slash J,
  $
  and each $a in J$ maps onto an ordered pair $(a', 0)$, where $a'$ is the image
  of $a$ in $S slash P_1$. Set $S slash P_1 = S'$ for convenience of notation,
  and let $k = (S slash J : overline(R))$. Then for $a in J$,
  $
    charpol_(overline(S) slash overline(R)) overline(a)
    = X^k dot charpol_(S' slash overline(R)) a'.
  $
  This implies at once that
  $
    T_(overline(S) slash overline(R)) overline(a)
    = T_(S' slash overline(R)) a', quad a in J.
  $
  If $S' slash overline(R)$ is inseparable, then $T_(S' slash overline(R))$ is
  the zero map, and thus by @eq:char-pol-reduction we have
  $T_(L slash K) (J) subset P$. This yields $J subset P frak(D)^(-1)$, whence
  $P_1 | frak(D)$. The reverse argument is equally simple: suppose that
  $S' slash overline(R)$ is separable. Then there exists an $a in J$ such that
  $T_(S' slash overline(R)) a' != 0$, and therefore
  $T_(L slash K) (J) subset.not P$. Hence $J subset.not P frak(D)^(-1)$, that
  is, $P_1 divides.not frak(D)$. This completes the proof of the first assertion
  of the theorem. The second assertion is an obvious consequence of the first.
]

=== Global fields <ss:global-fields>

A _global field_ $K$ is either an _algebraic number field_ (that is, a finite
extension of the rational field $bold(Q)$), or else a _function field_ (that is,
a finite extension of a field $k(X)$ of rational functions in an indeterminate
$X$ over a finite field $k$). A _prime_ of $K$ is an equivalence class of
valuations of $K$. We exclude once and for all the "trivial" valuation $phi$,
defined by $phi(0) = 0$, $phi(a) = 1$ for $a in K$, $a != 0$. If $K$ is an
algebraic number field, there are the archimedean or _infinite primes_, arising
from embeddings of $K$ in the complex field $bold(C)$, and the non-archimedean
or _finite primes_ of $K$, arising from discrete $P$-adic valuations of $K$,
with $P$ ranging over the distinct maximal ideals in the ring $algint {K}$ of
all algebraic integers in $K$. #idx("global field")#idx("function field")#idx(
  "infinite prime",
)#idx("finite prime")

#source(73)If $K$ is a function field, there are no archimedean primes, and the
non-archimedean or _finite primes_ arise from discrete valuation rings in $K$.
#idx("finite prime")
In this case, as well as in the number field case, the residue class field
associated with a finite prime $P$ is a finite field; let $cal(N)(P)$ denote the
number of elements in this residue class field (see
@rem:ramification-comments[(iv)]).

For each finite prime $P$ of a global field $K$, we _normalize_ the $P$-adic
valuation $phi_P$ by setting
$
  phi_P (a) = cal(N)(P)^(-v_P (a)), quad a in K, quad a != 0,
$
$phi_P (0) = 0$ (see §~@ss:localizations-valuations). If $P$ is a _real prime_
of $K$, that is, an infinite prime arising from an embedding $mu: K -> bold(R)$,
let
#idx("real prime")
$
  phi_P (a) = |mu(a)|, quad a in K.
$
If $P$ is a _complex prime_ of $K$, that is, an infinite prime arising from an
embedding $mu: K -> bold(C)$ such that $mu(K) subset.not bold(R)$, let
#idx("complex prime")
$
  phi_P (a) = |mu(a)|^2, quad a in K.
$
Thus we have a _normalized valuation_ $phi_P$ for each prime $P$ of $K$.
#idx("normalized valuation")

#theorem(title: [Product Formula])[
  Let $K$ be a global field. Then for each nonzero $a in K$, $phi_P (a) = 1$
  a.e., and
  $
    product_P phi_P (a) = 1,
  $
  where $P$ ranges over all primes of $K$.
  #idx("product formula", target: [@th:product-formula])
] <th:product-formula>

For global fields, there is a stronger version of @th:strong-approximation:

#theorem(title: [Very Strong Approximation Theorem])[
  Let $P_1, dots, P_n$ be distinct primes of $K$ (finite or infinite), and let
  $P_0$ be a fixed prime distinct from these. Given any elements
  $a_1, dots, a_n in K$ and any $epsilon > 0$, there exists an element $a in K$
  such that
  $
    phi_(P_i) (a - a_i) < epsilon, quad 1 <= i <= n, \
    phi_P (a) <= 1, quad P != P_0, P_1, dots, P_n.
  $
  #idx(
    "Very Strong Approximation Theorem",
    target: [@th:very-strong-approximation],
  )
] <th:very-strong-approximation>

#corollary[
  Let ${P_1, dots, P_n}$ be distinct primes of the algebraic number field $K$,
  and suppose that there exists an infinite prime $P_0$ of $K$ distinct from
  $P_1, dots, P_n$. Let $a_1, dots, a_n in K$ be such that $a_i in R_(P_i)$ if
  $P_i$ is a finite prime, where $R = algint {K}$. Let $0 < epsilon < 1$. Then
  there exists an $a in R$ such that
  $
    phi_(P_i) (a - a_i) < epsilon, quad 1 <= i <= n, \
    phi_P (a) < 1, quad P "infinite", quad P != P_0, P_1, dots, P_n.
  $
] <cor:approximation-integers>

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#source(74)Throughout, $R$ is an integral domain with quotient field $K$. Unless
otherwise stated, $R$ is assumed to be a Dedekind domain.

#exercise[
  Let $J$ be a nonzero ideal of $R$. Using @eq:gcd-lcm, find all ideals of $R$
  which contain $J$. Prove that $R slash J$ is an artinian and noetherian ring.
  Deduce from this that every finitely generated $R$-torsion $R$-module
  possesses an $R$-composition series.
] <exc:torsion-composition-series>

#exercise[
  Let $R$ be a principal ideal domain, and let $N subset M$ be $R$-lattices with
  $K N = K M$. Suppose that
  $
    M = dsum_(i=1)^r R m_i, quad N = dsum_(j=1)^r R n_j, quad
    n_j = sum alpha_(j i) m_i, quad alpha_(j i) in R.
  $
  Show that
  $
    ord_R M slash N = R dot det(alpha_(i j)).
  $
  #hint[@exc:order-ideal-determinant][After change of $R$-bases of $M$ and $N$,
    we may assume that the matrix $(alpha_(i j))$ is diagonal. Such basis
    changes have the effect of multiplying $det(alpha_(i j))$ by a unit factor
    from $R$, and thus do not change $R dot det(alpha_(i j))$. Finally, if
    $(alpha_(i j))$ is diagonal, it follows from @th:order-ideal-multiplicative
    that $ord_R M slash N$ is the principal ideal generated by the product of
    the diagonal entries.]
  <hint:order-ideal-determinant>
] <exc:order-ideal-determinant>

#exercise[
  Let $X$ be a finitely generated $R$-torsion module. Show that $ord_R X$ and
  $ann_R X$ have the same prime ideal factors, apart from multiplicities.
  Explain the connection between this result and
  @th:min-pol-of-element[Theorem].
] <exc:order-annihilator-primes>

#exercise[
  Let $R subset S$ be an inclusion of Dedekind domains, and let $X$ be any
  finitely generated $R$-module. Prove that
  $
    S times.o_R ord_R X = ord_S (S times.o_R X).
  $
  #hint[@exc:order-ideal-extension][By @th:finitely-generated-modules-structure
    it suffices to handle the cases $X = J$ and $X = R slash J$, with $J$ a
    nonzero ideal of $R$. The result is obvious for $X = J$, while for
    $X = R slash J$ it follows from
    Exercise~@exc:base-change-quotient.] <hint:order-ideal-extension>
] <exc:order-ideal-extension>

#exercise[
  Let $f in Hom_R (M, M)$, where $M$ is an $R$-lattice. Prove that
  $
    ord_R M slash f(M) = R dot det f,
  $
  where $det f$ is computed by extending $f$ to a $K$-linear transformation on
  $K M$. #hint[@exc:order-ideal-endomorphism][Use
    @th:localization-dedekind[(ii)] to reduce the problem to the case where $R$
    is a principal ideal domain, and then use
    Exercise~@exc:order-ideal-determinant.] <hint:order-ideal-endomorphism>
] <exc:order-ideal-endomorphism>

#exercise[
  Let $M$, $N$ be full $R$-lattices in a $K$-space $V$. Prove that $M_P = N_P$
  a.e.
  #hint[@exc:full-lattices-equal-ae][There exist nonzero $alpha, beta in R$ such
    that $alpha M subset N subset beta M$.]
  <hint:full-lattices-equal-ae>
] <exc:full-lattices-equal-ae>

#exercise[
  Let $R$ be any domain, $M$ a finitely generated $R$-module, and let
  $phi: M -> M^(**)$ be the evaluation map (see @eq:dual-module). Show that if
  $M$ is $R$-torsionfree, then $phi$ is monic. Show that $M^* = 0$ if and only
  if $M$ is an $R$-torsion module.
] <exc:evaluation-monic>

#exercise[
  Let $R$ be a noetherian integrally closed domain, and let $M$, $N$ be full
  $R$-lattices in a $K$-space $V$. Suppose that $M_P subset N_P$ for each
  minimal prime $P$ of $R$, and let $N$ be reflexive. Prove that $M subset N$.
] <exc:reflexive-local-inclusion>

#exercise[
  #source(75)Keeping the hypotheses and notation of
  §~@ss:ramification-index-residue-degree, prove that
  $
    N_(L slash K) (S a) = R dot N_(L slash K) (a), quad a in L.
  $
  #hint[@exc:norm-principal-ideal][Use @rem:ramification-comments[(iii)] and
    Exercise~@exc:order-ideal-endomorphism.] <hint:norm-principal-ideal>
] <exc:norm-principal-ideal>

#exercise[
  Prove that the symbols $e(P_i, L slash K)$ and $f(P_i, L slash K)$ defined in
  §~@ss:ramification-index-residue-degree are multiplicative for towers of
  separable extensions.
] <exc:ef-multiplicative>

#exercise[
  Prove that the different $frak(D)(S slash R)$ defined in
  §~@ss:different-discriminant is multiplicative for towers of separable
  extensions. #hint[@exc:different-tower][Let $L_2 supset L_1 supset K$ be such
    a tower, and let $S_i$ be the integral closure of $R$ in $L_i$, $i = 1, 2$.
    Set
    $
      T_i = T_(L_i slash K), quad frak(D)_i = frak(D)(S_i slash R), quad
      T' = T_(L_2 slash L_1), quad frak(D)' = frak(D)(S_2 slash S_1).
    $
    To prove that $frak(D)_2 = frak(D)_1 frak(D)'$, show the equivalence of the
    following statements, for $x in L_2$ (use
    Exercise~@exc:transitivity-trace-norm):
    $
      x in frak(D)_2^(-1); quad T_2 (x S_2) subset R; quad
      T_1 (S_1 dot T'(x S_2)) subset R; \
      T'(x S_2) subset frak(D)_1^(-1); quad
      x frak(D)_1 subset frak(D)'^(-1).
    $] <hint:different-tower>
] <exc:different-tower>

#exercise[
  Let $tau: V times V -> K$ be a nondegenerate symmetric $K$-bilinear form on a
  finite dimensional $K$-space $V$, and let $M$ be a full $R$-lattice in $V$.
  Define
  $
    tilde(M) = {x in V : tau(x, M) subset R}.
  $
  Show that $tilde(M)$ is a full $R$-lattice in $V$, and that
  $tilde(tilde(M)) = M$. #hint[@exc:dual-lattice-form][If $N = dsum R x_i$ is a
    full $R$-lattice in $V$, then $tilde(N) = dsum R y_j$, where
    $tau(x_i, y_j) = delta_(i j)$, and then $tilde(tilde(N)) = dsum R x_i = N$.
    Hence if $N_1 subset M subset N_2$ with $N_1$, $N_2$ $R$-free, we have
    $tilde(N)_1 supset tilde(M) supset tilde(N)_2$, whence $tilde(M)$ is a full
    $R$-lattice in $V$. To prove that $tilde(tilde(M)) = M$ in general, show
    that the process of forming $tilde(M)$ from $M$ commutes with localization,
    and thus the problem can be reduced to the case of
    $R_P$-lattices.] <hint:dual-lattice-form>
] <exc:dual-lattice-form>

#exercise[
  Keeping the notation of Exercise~@exc:dual-lattice-form, let $n = rank_R M$.
  Define the _discriminant ideal_ of $M$ with respect to $tau$ to be the
  $R$-ideal $d(M)$ in $K$ generated by
  #idx("discriminant (ideal)")
  $
    {det (tau(x_i, x_j))_(1 <= i, j <= n) : x_1, dots, x_n in M}.
  $
  Prove that $d(M_P) = d(M)_P$ for each maximal ideal $P$ of $R$. Show that if
  $M = dsum_(i=1)^n R x_i$, then
  $
    d(M) = R dot det (tau(x_i, x_j))_(1 <= i, j <= n).
  $
  If $N subset M$, where $N$ is another full $R$-lattice in $V$, prove that
  $
    d(N) = (ord_R M slash N)^2 dot d(M),
  $ <eq:discriminant-sublattice>
  and that $d(N) subset d(M)$. Deduce from this that $d(M) = d(N)$ if and only
  if $M = N$. #hint[@exc:discriminant-of-lattice][To prove
    @eq:discriminant-sublattice, first localize, and then write $R$ in place of
    $R_P$. Use the notation of Exercise~@exc:order-ideal-determinant. Then
    $
      d(N) = R dot det (tau(n_i, n_j))
      = R dot {det (alpha_(i j))}^2 dot det (tau(m_i, m_j)).
    $] <hint:discriminant-of-lattice>
] <exc:discriminant-of-lattice>

#exercise[
  Let $L = K(alpha)$ be a finite separable extension of $K$, and let
  #source(76)
  $
    f(X) = minpol_K alpha = product_(i=1)^n (X - alpha_i),
  $
  where $alpha_1 (= alpha), alpha_2, dots, alpha_n$ are the algebraic conjugates
  of $alpha$ over $K$. Define the _discriminant_ of $alpha$ as
  #idx("discriminant (of element)")
  $
    disc alpha = det (T_(L slash K) (alpha^i dot alpha^j))_(0 <= i, j <= n-1).
  $
  Prove that
  $
    disc alpha & = det mat(
                   delim: "[",
                   1, alpha_1, dots.c, alpha_1^(n-1);
                   1, alpha_2, dots.c, alpha_2^(n-1);
                   dots.v, dots.v, , dots.v;
                   1, alpha_n, dots.c, alpha_n^(n-1)
                 )^2 \
               & = product_(1 <= i < j <= n) (alpha_i - alpha_j)^2
                 = plus.minus N_(L slash K) (f'(alpha)),
  $
  where $f'(X)$ is the formal derivative of $f(X)$.
] <exc:discriminant-of-element>

#exercise[
  Keeping the above notation, let $f(X) in R[X]$, so $alpha$ is integral over
  $R$. Let $S$ be the integral closure of $R$ in $L$. Show that
  $
    R plus.o R alpha plus.o dots.c plus.o R alpha^(n-1) subset S,
  $
  and hence prove that the discriminant $d(S slash R)$ divides
  $R dot disc alpha$.
] <exc:discriminant-divides>

#exercise[
  Let $omega$ be a primitive $m$th root of 1 over $K$, where
  $op("char") K divides.not m$. Show that the only prime ideals of $R$ dividing
  $disc omega$ are those which divide $m$. Hence if $P divides.not R m$, then
  $P$ is unramified in the extension $K(omega)$ of $K$.
] <exc:cyclotomic-unramified>

#exercise[
  Give another proof of @th:lattices-reflexive by showing that every finitely
  generated free $R$-module is reflexive, and then proving that every finitely
  generated projective $R$-module is reflexive.
] <exc:reflexive-projective>
