#import "main-defs.typ": *
#import "statements.typ": *

== Localization <sec:localization>

=== Rings of quotients <ss:rings-of-quotients>

Throughout this section, $R$ denotes a commutative ring. A _multiplicative
subset_ of $R$ is a subset $S$ closed under multiplication, and such that
$0 in.not S$, $1 in S$. We introduce an equivalence relation on the Cartesian
product #source(40)$R times S$ by setting $(a, s) tilde (a', s')$ if and only if
$t(s a' - s' a) = 0$ for some $t in S$. Let $a slash s$ (or $s^(-1) a$) denote
the equivalence class of the pair $(a, s)$. Now define
#idx("multiplicative subset")
$
  a/s plus.minus b/t = (t a plus.minus s b)/(s t), quad
  a/s dot b/t = (a b)/(s t),
$
verifying that these operations are indeed well-defined. The set of symbols
${a slash s}$ then forms a commutative ring, denoted by $S^(-1) R$, with unity
element $1 slash 1$ and zero element $0 slash 1$. For $s in S$, we have
$
  (s slash 1) dot (1 slash s) = 1 slash 1,
$
so $s slash 1$ is a unit in $S^(-1) R$, with inverse $1 slash s$. Denoting
$1 slash s$ by $s^(-1)$, we obtain
$
  a slash s = (1 slash s)(a slash 1) = s^(-1) (a slash 1).
$
We shall call $S^(-1) R$ a _ring of quotients_ of $R$.
#idx("ring of quotients")

An element $a in R$ is an _$S$-torsion_ element if $t a = 0$ for some $t in S$.
The above discussion shows at once that $(a, s)$ lies in the zero class of
$S^(-1) R$ if and only if $a$ is an $S$-torsion element of $R$. There is a ring
homomorphism
#idx("torsion element")
$
  i: R -> S^(-1) R,
$
given by $i(x) = x slash 1$, $x in R$. Then $ker i$ is precisely the set of
$S$-torsion elements of $R$. The map $i$ permits us to view $S^(-1) R$ as
$R$-module.

If $R$ is an integral domain, the map $i$ may be regarded as an embedding of $R$
into $S^(-1) R$; in particular, if $S = R - {0}$, then $S^(-1) R$ is precisely
the quotient field of $R$. For an arbitrary ring $R$, the map $i$ is monic if
and only if $R$ is _$S$-torsionfree_ (that is, $R$ contains no nonzero
$S$-torsion elements, or equivalently, $S$ contains no divisors of zero).

#theorem[
  Let $S$ be a multiplicative subset of $R$. Then any ring homomorphism
  $phi: R -> R'$ which maps each element of $S$ onto a unit of $R'$, extends
  uniquely to a ring homomorphism $psi: S^(-1) R -> R'$ such that
  $psi compose i = phi$.
] <th:ring-of-quotients-universal>

#proof[
  Define
  $
    psi(a slash s) = phi(a) slash phi(s), quad a in R, quad s in S.
  $
  It is easily checked that $psi$ is the desired homomorphism. If also
  $psi' compose i = phi$, then
  $
    psi'(a slash s) = psi'(a slash 1) dot psi'(1 slash s)
    = phi(a) slash phi(s) = psi(a slash s),
  $
  so $psi = psi'$.
]

#corollary[
  Let $phi: R -> R'$ be a ring homomorphism mapping a multiplicative subset $S$
  of $R$ into a multiplicative subset $S'$ of $R'$. Then there is a #source(
    41,
  )unique ring homomorphism $psi: S^(-1) R -> S'^(-1) R'$ which extends $phi$,
  that is, $psi(a slash 1) = phi(a) slash 1$, $a in R$.
] <cor:ring-of-quotients-functorial>

=== Modules of quotients <ss:modules-of-quotients>

Let $S$ be a multiplicative subset of the commutative ring $R$, and $M$ any
$R$-module. We view $S^(-1) R$ as $R$-module by means of the canonical map
$i: R -> S^(-1) R$, and we form the $S^(-1) R$-module
$
  S^(-1) M = S^(-1) R times.o_R M.
$
We shall call $S^(-1) M$ a _module of quotients_. Each $x in S^(-1) M$ is then
expressible as a finite sum
#idx("module of quotients")
$
  x = sum a_i s_i^(-1) times.o m_i, quad a_i in R, quad s_i in S, quad
  m_i in M.
$
Set $s = product s_i in S$; then
$
  x = sum s^(-1) dot a_i s s_i^(-1) times.o m_i
  = s^(-1) times.o sum a_i s s_i^(-1) m_i = s^(-1) times.o m,
$
say. Denote $s^(-1) times.o m$ by $m slash s$; we have thus shown that every
element of $S^(-1) M$ is of the form $m slash s$ for some $m in M$, $s in S$. It
is easily checked that
$
  m slash s plus.minus m' slash s' = (s' m plus.minus s m') slash s s'.
$

We shall call an element $m$ of an $R$-module $M$ an _$S$-torsion element_ if
$s m = 0$ for some $s in S$. The collection of all $S$-torsion elements of $M$
is called the _$S$-torsion submodule_ of $M$, and is an $R$-submodule of $M$.
#idx("torsion element")#idx("torsion submodule")

#theorem[
  Let $M'$ be the $S$-torsion submodule of $M$. Then $m slash s = 0$ in
  $S^(-1) M$ if and only if $m in M'$.
] <th:module-of-quotients-zero>

#proof[
  If $m in M'$, then $t m = 0$ for some $t in S$, whence
  $
    m slash s = s^(-1) times.o m = (s t)^(-1) times.o t m = 0.
  $

  Conversely, suppose that $s^(-1) times.o m_0 = 0$ in $S^(-1) M$. Then
  $1 times.o m_0 = s(s^(-1) times.o m_0) = 0$, and therefore $1 times.o m_0$ is
  expressible as a finite sum of elements of $S^(-1) M$ of the following three
  types:
  $
    (u + u') times.o m - u times.o m - u' times.o m, quad
    u times.o (m + m') - u times.o m - u times.o m', \
    u a times.o m - u times.o a m,
  $
  with $u, u' in S^(-1) R$, $m, m' in M$, $a in R$. Choose $t in S$ to be a
  common denominator for all of the $u$'s which occur in these terms, so that
  $t u in R$ for each such $u$ (or more precisely, $t u in i(R)$). Let
  $
    R_1 = t^(-1) dot i(R) = {a slash t : a in R},
  $
  #source(42)an $R$-submodule of $S^(-1) R$.

  We shall now define a homomorphism
  $
    f: R_1 times.o_R M -> M slash M'
  $
  by setting
  $
    f(x times.o m) = t x m + M', quad x in R_1, quad m in M.
  $
  This map $f$ is well-defined, since if $x = a slash t = b slash t$ in $R_1$,
  then $a - b$ is an $S$-torsion element of $R$, and hence $(a - b) m in M'$.
  Consider now the element $1 times.o m_0$. From the manner in which $R_1$ was
  chosen, it is clear that $1 times.o m_0 = 0$ in $R_1 times.o_R M$. Therefore
  $f(1 times.o m_0) = 0$ in $M slash M'$, that is, $t m_0 in M'$. This implies
  that $m_0$ also lies in $M'$, which completes the proof of the theorem.
]

#corollary[
  The module of quotients $S^(-1) M$ coincides with the module whose elements
  are equivalence classes of ordered pairs $(m, s)$, with
  $(m, s) tilde (m', s')$ if and only if $s' m - s m'$ is an $S$-torsion element
  of $M$. The class of $(m, s)$ may be identified with the element
  $m slash s = s^(-1) times.o m$ in $S^(-1) M$.
] <cor:module-of-quotients-pairs>

The $S^(-1) R$-module $S^(-1) M$ may be viewed as an $R$-module by use of the
homomorphism $i: R -> S^(-1) R$; in other words, an element $a in R$ acts on
$S^(-1) M$ as left multiplication by the element $a slash 1$ of $S^(-1) R$. We
shall say that the element $a in R$ _acts invertibly_ on an $R$-module $X$ if
the mapping $x -> a x$, $x in X$, gives a one-to-one map of $X$ onto itself. It
is then clear that every element of $S$ acts invertibly on the module of
quotients $S^(-1) M$.
#idx("invertible action")

On the other hand, given any $R$-module $X$ on which every element of $S$ acts
invertibly, we can make $X$ into an $S^(-1) R$-module by defining
$
  (a slash s) dot x = s^(-1) dot a x, quad a in R, quad s in S, quad x in X.
$ <eq:invertible-action>
This is the unique way in which $X$ can be made into an $S^(-1) R$-module so as
to preserve the action of $R$ on $X$.

#theorem[
  Let $X$ be an $R$-module on which every element of $S$ acts invertibly, and
  make $X$ into an $S^(-1) R$-module by means of @eq:invertible-action. Then
  there is an $S^(-1) R$-isomorphism
  $
    S^(-1) R times.o_R X tilde.equiv X.
  $
  Further, for each $R$-module $Y$, every $R$-homomorphism $f: Y -> X$ extends
  canonically to an $S^(-1) R$-homomorphism $f': S^(-1) Y -> X$, given by the
  formula
  $
    f'(u times.o y) = u dot f(y), quad u in S^(-1) R, quad y in Y.
  $
] <th:invertible-action-iso>

#proof[
  By @cor:module-of-quotients-pairs, every element of $S^(-1) R times.o_R X$ is
  expressible as $s^(-1) times.o x$, with $s in S$, $x in X$. Denote this
  element by $x slash s$. By @cor:module-of-quotients-pairs we have
  $x slash s = x' slash s'$ if and #source(43)only if $s' x - s x'$ is an
  $S$-torsion element of $X$. But $S$ acts invertibly on $X$, so $X$ is
  $S$-torsion free. Thus $x slash s = x' slash s'$ if and only if $s' x = s x'$.

  Now define a mapping $theta: S^(-1) R times.o_R X -> X$ by setting
  $theta(x slash s) = s^(-1) x$, $x in X$, $s in S$. The preceding remarks imply
  that $theta$ is well-defined; for if $x slash s = x' slash s'$, then
  $s^(-1) x = s'^(-1) x'$. Clearly $theta$ is epic, and is an
  $S^(-1) R$-homomorphism. Finally, $theta$ is monic, since if
  $theta(x slash s) = 0$, then $s^(-1) x = 0$ and hence also $x = 0$. This
  proves the first part of the theorem. We omit the straightforward proof of the
  second part.
]

=== Flatness <ss:flatness>

Recall that an $R$-module is _flat_ if tensoring with it preserves exactness
(see §~@ss:projective-and-flat-modules). We shall now prove that every ring of
quotients $S^(-1) R$ is a flat $R$-module.

Given any $R$-homomorphism $f: L -> M$ of $R$-modules, there is an
$S^(-1) R$-homomorphism $f_*: S^(-1) L -> S^(-1) M$, defined by setting
$f_* = 1 times.o f$, where
$
  1 times.o f: S^(-1) R times.o_R L -> S^(-1) R times.o_R M.
$
Thus
$
  f_* (l slash s) = f(l) slash s, quad l in L, quad s in S.
$ <eq:localized-map>
Using this we prove

#theorem[
  Let $L stretch(->)^f M stretch(->)^g N$ be an $R$-exact sequence, and let
  $f_*$, $g_*$ be defined as in @eq:localized-map. Then
  $
    S^(-1) L stretch(-->)^(f_*) S^(-1) M stretch(-->)^(g_*) S^(-1) N
  $
  is an exact sequence of $S^(-1) R$-modules.
] <th:localization-exact>

#proof[
  Since $g f = 0$, we have $g_* f_* = (g f)_* = 0$. Now let $x in ker g_*$, and
  write $x = m slash s$, $m in M$, $s in S$. Then
  $
    0 = g_* (m slash s) = s^(-1) g(m),
  $
  so $1 times.o g(m) = 0$ in $S^(-1) N$. Hence there exists an element $t in S$
  such that $t dot g(m) = 0$, that is, $g(t m) = 0$. But $ker g = im f$, and so
  we may write $t m = f(l)$ for some $l in L$. Then
  $
    x = m slash s = t m slash t s = f_* (l slash t s) in im f_*.
  $
  This shows that $ker g_* = im f_*$. Finally, it is clear that $f_*$ and $g_*$
  are $S^(-1) R$-homomorphisms, which completes the proof.
]

For later use, we state a special case of @th:localization-exact:

#source(44)
#corollary[
  An inclusion $L subset M$ of $R$-modules induces an inclusion
  $S^(-1) L subset S^(-1) M$ of $S^(-1) R$-modules, and there is an
  $S^(-1) R$-isomorphism
  $
    S^(-1) (M slash L) tilde.equiv S^(-1) M slash S^(-1) L.
  $
] <cor:localization-quotient>

Recall that an $R$-module $M$ is _noetherian_ if its submodules satisfy the
ascending chain condition. A ring $Lambda$ is _(left) noetherian_ if $Lambda$ is
noetherian as left $Lambda$-module. Analogously, $M$ is _artinian_ if its
submodules satisfy the descending chain condition.

We wish to prove that the properties of being noetherian or artinian are
preserved under formation of rings or modules of quotients. This is best
accomplished by using the concept of "saturation". Let $L subset M$ be
$R$-modules; call $L$ an _$S$-saturated_#footnote[See Bourbaki,
  @bib:Bourbaki1961a[Algèbre Commutative], page 69 for this terminology.]
submodule of $M$ if $M slash L$ is $S$-torsionfree, that is, $M slash L$ has no
nonzero $S$-torsion elements. Equivalently, $L$ is $S$-saturated in $M$ if for
$m in M$, $s in S$, the inclusion $s m in L$ implies that $m in L$.
#idx("saturated")

#theorem[
  Let $i: M -> S^(-1) M$ be defined by $i(m) = 1 times.o m$, $m in M$. There is
  a one-to-one inclusion-preserving correspondence between the set of
  $S$-saturated submodules $X$ of the $R$-module $M$, and the set of
  $S^(-1) R$-submodules $X'$ of $S^(-1) M$, given by
  $
    X' = S^(-1) X, quad X = i^(-1) (X').
  $
] <th:saturated-correspondence>

#proof[
  Straightforward exercise for the reader.
]

As an immediate consequence of @th:saturated-correspondence, we obtain

#theorem[
  If $M$ is a noetherian $R$-module, then $S^(-1) M$ is a noetherian
  $S^(-1) R$-module. In particular, if $R$ is a noetherian ring, so is
  $S^(-1) R$. The analogous results hold true with "noetherian" replaced by
  "artinian".
] <th:localization-noetherian>

=== Localization at prime ideals <ss:localization-at-prime-ideals>

Let $R$ be a commutative ring, and let $J$, $J'$ denote ideals of $R$. We write
$J < J'$ to indicate that $J$ is properly contained in $J'$. Let us set
$
  R - J = {x : x in R, x in.not J}.
$

#definition(kind: "Definitions")[
  + $J$ is a _proper_ ideal if $J < R$.
  + $J$ is a _maximal_ ideal if $J < R$, and if there is no ideal $J'$ such that
    $J < J' < R$.
  + $J$ is a _prime_ ideal if $J < R$, and $R slash J$ has no zero divisors.
] <def:proper-maximal-prime>
#idx("proper ideal")#idx("maximal ideal")#idx("prime ideal")#idx(
  "ideal",
  "proper",
)#idx("ideal", "maximal")#idx("ideal", "prime")

Clearly, a proper ideal $J$ is prime if and only if its complement $R - J$ is a
multiplicative set. Starting with a prime ideal $P$ of $R$, we may form the
multiplicative set $S = R - P$, and then define a ring of quotients $S^(-1) R$.
#source(45)This ring, hereafter denoted by $R_P$, is called the _localization_
of $R$ at $P$. Since every element of $R - P$ is invertible in $R_P$, it is
easily verified that $R_P$ has a unique maximal ideal, namely $P dot R_P$. We
should remark that the ring homomorphism $i: R -> R_P$, defined in
§~@ss:rings-of-quotients, enables us to view $R_P$ (and all $R_P$-modules) as
$R$-modules. Thus $P dot R_P$ is the same as $i(P) dot R_P$.
#idx("localization")

If $R$ happens to be an integral domain, then the mapping $i: R -> R_P$ is an
embedding. In particular, when $P = {0}$ then $R_P$ is precisely the quotient
field of the domain $R$.

Returning to the general case, let $M$ be any $R$-module. We define
$M_P = R_P times.o_R M$, an $R_P$-module called the _localization_ of $M$ at
$P$.

#theorem[
  Localization at maximal ideals does not affect residue class modules.
  Specifically, let $P$ be a maximal ideal of $R$, and let $M$ be an $R$-module.
  Then for each $r > 0$, we may view $M slash P^r dot M$ as an $R_P$-module, and
  there is an $R_P$-isomorphism
  $
    M slash P^r dot M tilde.equiv M_P slash P^r dot M_P.
  $
] <th:localization-residue-modules>

#proof[
  Let $S = R - P$, and put $overline(M) = M slash P^r dot M$. We show first that
  $overline(M)$ can be made into an $R_P$-module. For each $s in S$ we have
  $R s + P = R$, since $P$ is maximal. Hence there exist elements $alpha in R$,
  $pi in P$, such that $alpha s + pi = 1$. Taking $r$th powers, we obtain
  $
    beta s + pi^r = 1
  $
  for some $beta in R$. Therefore $s$ is a unit in the ring $R slash P^r$, and
  hence acts invertibly on the $(R slash P^r)$-module $overline(M)$. From
  @th:invertible-action-iso we deduce that $overline(M)$ can be viewed as
  $R_P$-module, and that there is an $R_P$-isomorphism
  $
    overline(M) tilde.equiv R_P times.o_R overline(M) = (overline(M))_P.
  $
  But by @cor:localization-quotient we have
  $
    (overline(M))_P = (M slash P^r dot M)_P tilde.equiv
    M_P slash P^r dot M_P.
  $
  Hence there is an $R_P$-isomorphism
  $overline(M) tilde.equiv M_P slash P^r dot M_P$, and the theorem is proved.
]

The preceding theorem is used most frequently for the special case where
$r = 1$, and yields the $(R slash P)$-isomorphism
$
  M slash P dot M tilde.equiv M_P slash P dot M_P
$ <eq:residue-module-local>
for each maximal ideal $P$ of $R$, and each $R$-module $M$.

We often refer to problems concerning $R$-modules and $R$-homomorphisms as
_global_ problems, whereas those involving $R_P$-modules are called _local_
problems. A fundamental technique in algebraic number theory, and in its
generalizations considered in this book, is the method of solving global
#source(46)questions by first settling the local case, and then applying this
local information to the global case. The next few theorems provide some
connections between local and global information. #idx("global problem")#idx(
  "local problem",
)

For each $R$-module $M$, and each prime ideal $P$ of $R$, there is an
$R$-homomorphism
$
  i_P: M -> M_P,
$
given by $i_P (m) = 1 times.o m in R_P times.o_R M$, $m in M$. Consequently
there is an $R$-homomorphism $M -> product_P M_P$, where $P$ ranges over all
maximal ideals of $R$.

#theorem[
  The map $M -> product_P M_P$ is monic. In particular, $M = 0$ if and only if
  $M_P = 0$ for each maximal ideal $P$ of $R$.
] <th:local-global-zero>

#proof[
  Denote the above map by $f$, and suppose that $m in ker f$. Set
  $
    J = {a in R : a dot m = 0},
  $
  an ideal in $R$. If $J < R$, then#footnote[This statement is a consequence of
    Zorn's Lemma (see Curtis–Reiner [@bib:Curtis1962]); it does not require the
    hypothesis that $R$ be noetherian.] $J$ is contained in some maximal ideal
  $P$ of $R$. But $i_P (m) = 0$, so by @th:module-of-quotients-zero there exists
  an $s in R - P$ such that $s dot m = 0$. Hence $s in J$, $s in.not P$, which
  contradicts the fact that $J subset P$. This shows that $J = R$, and thus
  $m = 0$ as claimed. The second assertion in the theorem is then obvious.
]

#corollary[
  Let $f in Hom_R (L, M)$ induce $f_P: L_P -> M_P$. Then
  + There are $R_P$-isomorphisms
    $
      (ker f)_P tilde.equiv ker f_P, quad (im f)_P tilde.equiv im f_P, quad
      (cok f)_P tilde.equiv cok f_P,
    $
    for each maximal ideal $P$ of $R$.
  + $f$ is monic if and only if each $f_P$ is monic.
  + $f$ is epic if and only if each $f_P$ is epic.
  + A sequence of $R$-modules
    $
      0 -> L stretch(->)^f M stretch(->)^g N -> 0
    $
    is exact if and only if the sequence
    $
      0 -> L_P stretch(->)^(f_P) M_P stretch(->)^(g_P) N_P -> 0
    $
    is exact for each $P$.
] <cor:local-global-exact>

#proof[
  Given any $f in Hom_R (L, M)$, there is an $R$-exact sequence
  #source(47)
  $
    0 -> ker f -> L stretch(->)^f M.
  $
  Since $R_P$ is $R$-flat, it follows that the sequence
  $
    0 -> (ker f)_P -> L_P stretch(->)^(f_P) M_P
  $
  is $R_P$-exact. This gives an $R_P$-isomorphism
  $(ker f)_P tilde.equiv ker f_P$. Similar arguments yield the other assertions
  in (i).

  If $f$ is monic, then $ker f = 0$, whence $ker f_P = 0$ for each $P$, by (i).
  Conversely, if each $f_P$ is monic, then by (i) and @th:local-global-zero,
  also $f$ is monic. This proves (ii), and the remaining assertions in the
  theorem follow in a similar manner.
]

#corollary[
  Let $R$ be an integral domain with quotient field $K$, and regard $R$ and all
  of its localizations $R_P$ as embedded in $K$. Then
  $
    R = inter.big_P R_P,
  $
  where $P$ ranges over all maximal ideals of $R$.
] <cor:domain-intersection-of-localizations>

#proof[
  Obviously, $R$ is contained in the intersection. Conversely, let $x in K$ be
  such that $x in R_P$ for all $P$. Writing $x = a slash b$, $a, b in R$, it
  follows that $a in b R_P$ for all $P$. Let $f: R -> R$ be defined by
  $f(r) = r b$, $r in R$. Then the image of $a$ in $cok f_P$ is zero for all
  $P$. But by @th:local-global-zero and @cor:local-global-exact, the map
  $
    cok f -> product_P cok f_P
  $
  is monic. Hence $a$ has zero image in $cok f$, that is, $a in b R$. This shows
  that $x in R$, so $R$ contains $inter.big R_P$, and the proof is complete.
]

The reader should be cautioned that @cor:domain-intersection-of-localizations
does not hold for arbitrary commutative rings $R$, nor does it generalize to the
case of $R$-modules unless additional hypotheses are imposed.

Let us next record the following special cases of @th:change-of-rings-iso and
the "Change of rings" @th:change-of-rings-ext[Theorem].

#theorem[
  Let $Lambda$ be an $R$-algebra, where $R$ is a commutative ring, and let $M$
  be any finitely presented left $Lambda$-module. Then for every $Lambda$-module
  $N$, and for each prime ideal $P$ of $R$, there is an $R_P$-isomorphism
  $
    R_P times.o_R Hom_Lambda (M, N) tilde.equiv Hom_(Lambda_P) (M_P, N_P).
  $
] <th:localization-hom>

#theorem[
  Let $Lambda$ be a left noetherian $R$-algebra, where $R$ is a commutative
  ring, and let $P$ be any prime ideal of $R$. Then there is an
  $R_P$-isomorphism
  $
    R_P times.o_R Ext_Lambda^n (M, N) tilde.equiv
    Ext_(Lambda_P)^n (M_P, N_P), quad n >= 0,
  $
  for each pair of left $Lambda$-modules $M$, $N$ such that $M$ is finitely
  generated over $Lambda$.
] <th:localization-ext>

#source(48)We may emphasize that when $R$ is noetherian, and $Lambda$ is
finitely generated as $R$-module, then $Lambda$ is left and right noetherian,
and every finitely generated $Lambda$-module is automatically finitely
presented.

Now let $Lambda$ be any $R$-algebra; we shall show that the question, as to
whether a given $Lambda$-exact sequence is $Lambda$-split, is a "local"
question, that is, the answer is determined by the answers for the corresponding
$Lambda_P$-sequences, where $P$ ranges over the maximal ideals of $R$.

#theorem[
  Let $Lambda$ be an algebra over the commutative ring $R$, and let
  $
    0 -> L stretch(->)^f M stretch(->)^g N -> 0
  $ <eq:split-global>
  be a $Lambda$-exact sequence, where $N$ is a finitely presented
  $Lambda$-module. Then the sequence is $Lambda$-split if and only if for each
  maximal ideal $P$ of $R$, the $Lambda_P$-exact sequence
  $
    0 -> L_P stretch(->)^(f_P) M_P stretch(->)^(g_P) N_P -> 0
  $ <eq:split-local>
  is $Lambda_P$-split.
] <th:splitting-local>

#proof[
  The epimorphism $g$ induces a map
  $
    g_*: Hom_Lambda (N, M) -> Hom_Lambda (N, N).
  $
  We claim that the sequence @eq:split-global is split if and only if $g_*$ is
  epic. Indeed, if $h: N -> M$ is such that $g h = 1_N$, the identity map on
  $N$, then for each $phi in Hom_Lambda (N, N)$ we have
  $h phi in Hom_Lambda (N, M)$, and
  $
    g_* (h phi) = g h dot phi = phi.
  $
  Thus if @eq:split-global splits, then $g_*$ is epic. Conversely, if $g_*$ is
  epic, there exists an $h in Hom_Lambda (N, M)$ such that $g_* h = 1_N$, that
  is, $g h = 1_N$. This completes the proof of the claim.

  Now let us define
  $
    (g_P)_*: Hom_(Lambda_P) (N_P, M_P) -> Hom_(Lambda_P) (N_P, N_P),
  $
  where $g$ induces $g_P: M_P -> N_P$. By virtue of @th:localization-hom, we may
  identify $(g_P)_*$ with $(g_*)_P$. We have seen above that @eq:split-global is
  $Lambda$-split if and only if $g_*$ is epic, while analogously @eq:split-local
  is $Lambda_P$-split if and only if $(g_*)_P$ is epic. The theorem then follows
  immediately from @cor:local-global-exact.
]

#corollary[
  Let $Lambda$ be an $R$-algebra, $N$ a finitely presented left $Lambda$-module.
  Then $N$ is $Lambda$-projective if and only if $N_P$ is $Lambda_P$-projective
  for each $P$.
] <cor:projective-local>

#proof[
  Choose a free $Lambda$-module $F$ mapping onto $N$, so there is a
  $Lambda$-exact #source(49)sequence $0 -> L -> F -> N -> 0$. If $N$ is
  projective, then $N | F$, whence $N_P | F_P$ and $N_P$ is
  $Lambda_P$-projective. Conversely, if each $N_P$ is projective, then each
  localization of the above sequence is split. Hence the original sequence
  splits, by @th:splitting-local, and so $N$ is projective.
]

Recall that $Lambda$ is a _left hereditary_ ring if every left ideal of $Lambda$
is projective. We have at once

#corollary[
  Let $Lambda$ be a left noetherian $R$-algebra, where $R$ is a commutative
  ring. Then $Lambda$ is left hereditary if and only if the ring $Lambda_P$ is
  left hereditary for every maximal ideal $P$ of $R$.
] <cor:hereditary-local>

#proof[
  Suppose that $Lambda_P$ is left hereditary for each $P$, and let $L$ be any
  left ideal of $Lambda$. Then $L$ is finitely presented as $Lambda$-module,
  since $Lambda$ is left noetherian. Further, $L_P$ is a left ideal of
  $Lambda_P$, and hence $L_P$ is projective. Therefore $L$ is projective, by
  @cor:projective-local.

  Conversely, let $Lambda$ be left hereditary, and let $P$ be any maximal ideal
  of $R$. By @th:saturated-correspondence, every left ideal of $Lambda_P$ is of
  the form $L_P$, for some left ideal $L$ of $Lambda$. Since $L$ is projective
  as $Lambda$-module, it follows as in @cor:projective-local that $L_P$ is
  $Lambda_P$-projective, as desired. This completes the proof of the corollary.
]

In order to generalize @cor:hereditary-local, we introduce the concept of
homological dimension, which is sometimes referred to as "projective dimension".
The _homological dimension_ $hd_Lambda M$ of a left $Lambda$-module $M$ is the
least nonnegative integer $n$ for which there exists a $Lambda$-exact sequence
#idx("homological dimension")
$
  0 -> X_n -> X_(n-1) -> dots.c -> X_0 -> M -> 0, quad X_i "projective".
$ <eq:projective-resolution-length>
We set $hd_Lambda M = infinity$ if no such $n$ exists. Once
@eq:projective-resolution-length is given, it follows directly from definition
@eq:ext-n that $Ext_Lambda^r (M, dot) = 0$, $r >= n + 1$. (The notation
$Ext_Lambda^r (M, dot) = 0$ means that $Ext_Lambda^r (M, L) = 0$ for each
$Lambda$-module $L$.)

Now consider a $Lambda$-exact sequence
$
  0 -> K_n -> X_(n-1) -> dots.c -> X_0 -> M -> 0, quad X_i "projective".
$ <eq:syzygy-sequence>
By @eq:dimension-shifting there is an isomorphism
$
  Ext_Lambda^(n+k) (M, dot) tilde.equiv Ext_Lambda^k (K_n, dot).
$
But by @rem:ext-properties[(v)], $K_n$ is projective if and only if
$Ext_Lambda^1 (K_n, dot) = 0$. This gives

#theorem[
  Let $M$ be a left $Lambda$-module. The following statements are equivalent:
  + $hd_Lambda M <= n$.
  + $Ext_Lambda^r (M, dot) = 0$ for $r >= n + 1$.
  + #source(50)For every exact sequence @eq:syzygy-sequence in which
    $X_0, dots, X_(n-1)$ are projective, also $K_n$ is projective.
] <th:homological-dimension-criteria>

We note that $hd_Lambda M = 0$ if and only if $M$ is projective. The following
result is thus a generalization of @cor:projective-local:

#theorem[
  Let $Lambda$ be a left noetherian $R$-algebra, where $R$ is a commutative
  ring, and let $M$ be any finitely generated left $Lambda$-module. Then
  $
    hd_Lambda M = sup_P {hd_(Lambda_P) M_P},
  $
  where $P$ ranges over all maximal ideals of $R$.
] <th:homological-dimension-local>

#proof[
  Denote the sup by $s$, and let $n = hd_Lambda M$. We show first that $n >= s$.
  The result is clear if $n = infinity$, so assume $n$ finite. Then there is an
  exact sequence @eq:projective-resolution-length with each $X_i$ projective.
  Localizing at $P$, we obtain a projective resolution of $M_P$, and therefore
  $hd_(Lambda_P) M_P <= n$. This holds for each $P$, whence $s <= n$, as
  claimed.

  Conversely, we prove that $n <= s$, and we may assume that $s$ is finite. From
  @th:localization-ext we obtain
  $
    R_P times.o_R Ext_Lambda^(s+1) (M, N) = 0
  $
  for all $P$ and for all $Lambda$-modules $N$. It now follows from
  @th:local-global-zero that $Ext_Lambda^(s+1) (M, dot) = 0$, and so
  $hd_Lambda M <= s$. This completes the proof of the theorem.
]

The _left global dimension_ of $Lambda$ is defined as
#idx("global dimension")
$
  dim Lambda = sup {hd_Lambda M : M = "left" Lambda"-module"}.
$
(We should really use the notation $op("l. gl. dim.") Lambda$, but will employ
the simpler notation $dim Lambda$ when there is no danger of confusion.)
Clearly, $dim Lambda = 0$ if and only if every left $Lambda$-module is
projective, that is, if and only if $Lambda$ is a semisimple artinian ring (see
§~@ss:wedderburn-theorem).

We claim that $dim Lambda <= 1$ if and only if $Lambda$ is left hereditary.
Suppose that $dim Lambda <= 1$, and let $J$ be any left ideal of $Lambda$. There
is a $Lambda$-exact sequence
$
  0 -> J -> Lambda -> Lambda slash J -> 0,
$
in which $Lambda$ is projective. Since
$hd_Lambda Lambda slash J <= dim Lambda <= 1$, it follows from
@th:homological-dimension-criteria that $J$ is projective, as desired.
Conversely, let $Lambda$ be left hereditary, and let $M$ be any left
$Lambda$-module. There is a $Lambda$-exact sequence
$
  0 -> K -> F -> M -> 0,
$
in which $F$ is $Lambda$-free. Since $Lambda$ is hereditary, the submodule $K$
of the free module $F$ must be projective, by @th:hereditary-submodules-of-free.
Therefore $hd_Lambda M <= 1$ for each $M$, whence also $dim Lambda <= 1$.

#source(51)We are now ready to give a generalization of @cor:hereditary-local.

#theorem[
  Let $Lambda$ be a left noetherian $R$-algebra, where $R$ is a commutative
  ring. Then
  $
    dim Lambda = sup_P {dim Lambda_P},
  $
  where $P$ ranges over all maximal ideals of $R$.
] <th:global-dimension-local>

#proof[
  We shall use a formula due to M. Auslander (see Rotman [@bib:Rotman1970,
  Th.~9.14]):
  $
    dim Lambda = sup {hd_Lambda Lambda slash J : J = "left ideal of" Lambda}.
  $
  But $Lambda slash J$ is a finitely generated $Lambda$-module, so by
  @th:homological-dimension-local
  $
    hd_Lambda Lambda slash J = sup_P {hd_(Lambda_P) Lambda_P slash J_P}.
  $
  Further, by @th:saturated-correspondence, as $J$ ranges over all left ideals
  of $Lambda$, $J_P$ ranges over all left ideals of $Lambda_P$. Therefore we
  have
  $
    dim Lambda = sup_(J, P) {hd_(Lambda_P) Lambda_P slash J_P}
    = sup_P {dim Lambda_P},
  $
  as claimed.
]

To conclude this section, let us show that homological and global dimensions are
unchanged by passage to $P$-adic completions. The preceding theorems reduce the
calculations of $hd_Lambda M$ and $dim Lambda$ to the case where the ground ring
is $R_P$, a local ring. If we make the additional hypothesis that $R$ is
noetherian, then each $R_P$ is also noetherian. The $P$-adic completion
$hat(R)_P$ of the ring $R_P$ is then a faithfully flat $R_P$-module (see remark
following @cor:completion-faithfully-flat, or
Exercise~@exc:completion-faithfully-flat). Using this fact, we prove

#theorem[
  Let $hat(R)_P$ be the $P$-adic completion of the local noetherian ring $R_P$,
  and let $Lambda_P$ be a left noetherian $R_P$-algebra. Set
  $
    hat(Lambda)_P = hat(R)_P times.o_(R_P) Lambda_P, quad
    hat(M)_P = hat(R)_P times.o_(R_P) M_P,
  $
  where $M_P$ is any finitely generated left $Lambda_P$-module. Then
  $
    hd_(Lambda_P) M_P = hd_(hat(Lambda)_P) hat(M)_P
  $
  for each $M_P$. Furthermore
  $
    dim Lambda_P = dim hat(Lambda)_P.
  $
] <th:dimension-completion>

#proof[
  As in the proof of @th:homological-dimension-local, we find at once that
  $hd hat(M)_P <= hd M_P$. On the other hand, if $s = hd hat(M)_P$, then for
  each $Lambda_P$-module $N_P$ we have
  $
    hat(R)_P times.o_(R_P) Ext_(Lambda_P)^(s+1) (M_P, N_P) = 0.
  $
  #source(52)Since $hat(R)_P$ is faithfully flat as $R_P$-module, it follows
  that $Ext^(s+1) (M_P, dot) = 0$, and therefore $hd M_P <= s$. The remaining
  assertion in @th:dimension-completion follows from the formula of Auslander
  used in the proof of @th:global-dimension-local.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $R$ be a domain with quotient field $K$, and let $M$ be a direct summand
  of a free $R$-module $F$ of rank $n$. Show that $M$ and all of its
  localizations $M_P$, where $P$ ranges over the maximal ideals of $R$, may be
  embedded in the $n$-dimensional vector space $K times.o_R F$ over $K$. Then
  use @cor:domain-intersection-of-localizations to prove the formula
  $
    M = inter.big M_P,
  $
  the intersection being taken over all maximal ideals $P$ of $R$.
] <exc:module-intersection-of-localizations>

#exercise[
  Let $R$ be a domain with quotient field $K$, and let $X$, $Y$ be submodules of
  an $R$-module $M$. Show that if $X_P = Y_P$ in $M_P$ for each $P$, then
  $X = Y$. #hint[@exc:submodules-equal-locally][For each $P$,
    ${(X + Y) slash Y}_P = 0$.] <hint:submodules-equal-locally>
] <exc:submodules-equal-locally>

#exercise[
  Let $R$ be a commutative ring, and let $S$, $T$ be multiplicative subsets of
  $R$ such that $S subset T$. Prove that $T^(-1) R$ is isomorphic to the ring of
  quotients of $S^(-1) R$ relative to the multiplicative set which is the image
  of $T$ in $S^(-1) R$.
] <exc:quotients-transitive>

#exercise[
  Let $P_1, dots, P_n$ be a set of prime ideals of the commutative ring $R$, no
  one of which contains another, and let
  $
    S = R - (P_1 union dots union P_n).
  $
  + Show that $S$ is a multiplicative subset of $R$, and that the distinct
    maximal ideals of $S^(-1) R$ are $P_i dot S^(-1) R$, $1 <= i <= n$.
  + Show that $R_(P_i)$ is canonically isomorphic to the localization of
    $S^(-1) R$ at the maximal ideal $P_i dot S^(-1) R$.
  + Show that
    $
      S^(-1) R = inter.big_(i=1)^n R_(P_i)
    $
    if $R$ is an integral domain, the intersection being formed within the
    quotient field of $R$. (Reference: Bourbaki [@bib:Bourbaki1961a, Ch.~II,
    §~3, no.~5].)
] <exc:semilocal-ring>

#exercise[
  Let $S$ be a multiplicative subset of the commutative ring $R$, and let
  $R' = S^(-1) R$. Let $Lambda$ be an $R$-algebra, and set
  $Lambda' = R' times.o_R Lambda$, an $R'$-algebra. Show that every finitely
  generated left $Lambda'$-module $X$ contains a finitely generated left
  $Lambda$-module $M$ such that
  $
    Lambda' times.o_Lambda M tilde.equiv Lambda' M = X.
  $
  #hint[@exc:lattice-generating-localization][The ring homomorphism
    $Lambda -> Lambda'$ makes $X$ into a left $Lambda$-module. Let
    $
      X = sum_(i=1)^n Lambda' x_i, quad "and set" quad
      M = sum_(i=1)^n Lambda x_i, quad "so" quad Lambda' M = X.
    $
    The inclusion $M subset X$ yields an inclusion
    $Lambda' times.o_Lambda M subset Lambda' times.o_Lambda X tilde.equiv X$,
    since $R'$ is $R$-flat. Hence the map
    $Lambda' times.o_Lambda M -> Lambda' M$ is monic, and thus is an
    isomorphism. For another approach, see
    Exercise~@exc:jordan-zassenhaus-quotients.]
  <hint:lattice-generating-localization>
] <exc:lattice-generating-localization>
