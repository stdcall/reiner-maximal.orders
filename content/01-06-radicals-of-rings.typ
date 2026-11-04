#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/01-06-radicals-of-rings.typ": lifted-isomorphism
#import "diagrams/04-15-progenerators.typ": arrow-pair

== Radicals of rings <sec:radicals-of-rings>

Throughout this section, $A$ is a ring (with unity element), not necessarily
commutative. All modules are unital. For an $A$-module $M$, define its
_annihilator_ as
#idx("annihilator")
$
  ann_A M = {a in A : a M = 0},
$
and omit the subscript $A$ when there is no danger of confusion. We shall also
write $Hom$ instead of $Hom_A$. By an _epimorphism_ $A -> B$ of the ring $A$
onto the ring $B$, we shall mean always a ring homomorphism which is surjective.
(This represents a change from the terminology used in category theory.) As
general reference for the material in this section, we cite Jacobson
[@bib:Jacobson1943, @bib:Jacobson1956].
#idx("epimorphism (of rings)")

=== Jacobson radical <ss:jacobson-radical>

An $A$-module $M$ is _irreducible_ (or _simple_) if $M != 0$ and $M$ contains no
submodules except 0 and $M$. If $M$ is simple, then for each nonzero $m in M$ we
have $M = A m$. The module epimorphism $A -> M$ defined by $a -> a m$, $a in A$,
has kernel a left ideal $L$ in $A$, and thus $M tilde.equiv A slash L$. Since
$M$ is simple, $L$ must be a maximal left ideal of $A$. Conversely, for each
such $L$, the $A$-module $A slash L$ is simple. #idx("irreducible")#idx(
  "simple (module)",
)

The _Jacobson radical_ of $A$, denoted by $rad A$, is defined as #idx(
  "Jacobson radical",
)#idx("radical")
$
  rad A = inter.big_M ann M = inter.big_L ann A slash L,
$ <eq:jacobson-radical>
where $M$ ranges over all simple left $A$-modules, and $L$ over all maximal left
ideals of $A$. Since each $ann M$ is a two-sided ideal of $A$, so is $rad A$.

#source(87)The ring $A$ is _semisimple_ if $rad A = 0$. (Some authors call such
rings "semisimple in the sense of Jacobson".)
#idx("semisimple (ring)")

#theorem[
  $A slash rad A$ is a semisimple ring.
] <th:quotient-by-radical-semisimple>

#proof[
  Let $overline(A) = A slash rad A$; since $(rad A) M = 0$ for each simple left
  $A$-module $M$, we may view $M$ as a simple $overline(A)$-module. Now let
  $x in A$ be such that $x + rad A in rad overline(A)$. Then
  $(x + rad A) M = 0$, whence $x M = 0$. Hence $x in rad A$, which shows that
  $rad overline(A) = 0$, and so $overline(A)$ is semisimple.
]

#theorem[
  $rad A$ is the intersection of all maximal left ideals of $A$.
] <th:radical-maximal-left-ideals>

#proof[
  For each maximal left ideal $L$ of $A$ we have $ann (A slash L) subset L$,
  since $A$ has a unity element. Therefore
  $
    rad A = inter.big_L ann (A slash L) subset inter.big_L L.
  $
  For the reverse inclusion, let $M$ be any simple $A$-module. Then
  $
    ann M = inter.big_(m in M) ann m.
  $
  But if $m in M$, $m != 0$, then $ann m$ is the kernel of the epimorphism
  $A -> A m = M$, and so $ann m$ is a maximal left ideal of $A$. Hence
  $
    ann M supset inter.big_L L,
  $
  where $L$ ranges over all maximal left ideals of $A$. Therefore
  $
    rad A = inter.big_M ann M supset inter.big_L L,
  $
  and the theorem is proved.
]

An element $u in A$ is a _unit_ if there exists an element $v in A$ such that
$u v = v u = 1$. We shall denote by $u(A)$ the group of units of $A$. In most of
the cases arising in this book, each element of $A$ having a one-sided inverse
is necessarily a unit of $A$. To prove this, we begin with a result of
independent interest:
#idx("unit")

#theorem-variant([@th:radical-maximal-left-ideals], suffix: "a")[
  Let $M$ be a noetherian left $A$-module, and let $f in Hom_A (M, M)$ be such
  that $f(M) = M$. Then $f$ is an isomorphism.
] <th:surjective-endomorphism-noetherian>

#proof[
  We need only show that $f$ is monic. For $n >= 1$, set
  $
    K_n = ker f^n = {x in M : f^n (x) = 0}.
  $
  Then $0 subset K_1 subset K_2 subset dots.c$ is an ascending chain of
  submodules of $M$, and #source(88)hence $K_n = K_(n+1)$ for some $n$, since
  $M$ is noetherian. Now let $x in M$ be such that $f(x) = 0$. From the
  hypothesis that $f(M) = M$, it follows that $M = f^n (M)$, and so we may write
  $x = f^n (y)$ for some $y in M$. Then $0 = f(x) = f^(n+1) (y)$, whence
  $y in K_(n+1)$. But then $y in K_n$, and thus $x = f^n (y) = 0$. This
  completes the proof that $f$ is monic, and establishes the theorem.
]

As an immediate consequence of the above, we have

#theorem[
  Let $A$ be a left noetherian ring, and let $a b = 1$ in $A$. Then also
  $b a = 1$.
] <th:one-sided-inverse-noetherian>

#proof[
  Let $M = lmodule(A, A)$, a noetherian left $A$-module; by
  @th:surjective-endomorphism-noetherian, every $A$-epimorphism $f: M -> M$ must
  be an isomorphism. Since
  $
    A = A a b subset A b subset A,
  $
  we have $A = A b$. Let $f: M -> M$ be the epimorphism defined by setting
  $f(x) = x b$, $x in M$. Then $f$ is an isomorphism. However,
  $f(1 - b a) = (1 - b a) b = 0$, and therefore $1 - b a = 0$. This completes
  the proof.
]

Returning to the general case, we prove next

#theorem[
  For any ring $A$,
  $
    rad A = {x in A : 1 - a x b in u(A) "for all" a, b in A}.
  $
] <th:radical-units>

#proof[
  (i) Let $x in rad A$, and let $a, b in A$; since $rad A$ is a two-sided ideal
  of $A$, we have $y = a x b in rad A$. We now show that $1 - y in u(A)$ for
  each $y in rad A$. If $A(1 - y) < A$, there is a maximal left ideal $L$ of $A$
  such that $A(1 - y) subset L$, and then $1 - y in L$. Since $rad A subset L$,
  this gives $1 in L$, a contradiction. Therefore $A(1 - y) = A$ for all
  $y in rad A$, and so $t(1 - y) = 1$ for some $t in A$. Therefore
  $1 - t = -t y in rad A$, whence (as above) $A(1 - (1 - t)) = A$, that is
  $A t = A$. Hence there exists $u in A$ such that $u t = 1$, and thus
  $
    u = u t (1 - y) = 1 - y.
  $
  This proves that $t$ is a two-sided inverse of $1 - y$, so $1 - y in u(A)$, as
  desired.

  (ii) Let $x in A$ be such that $1 - a x b in u(A)$ for all $a, b in A$. To
  show that $x in rad A$, we need prove that $x M = 0$ for every simple left
  $A$-module $M$. Let $m in M$, $m != 0$; if $x m != 0$, then $M = A dot x m$,
  so $m = a x m$ for some $a in A$, and thus $(1 - a x) m = 0$. But
  $1 - a x in u(A)$, and hence $m = 0$, a contradiction. This proves that
  $x m = 0$ for each nonzero $m in M$, and therefore $x M = 0$, completing the
  proof of the theorem.
]

#corollary[
  If we compute a radical of $A$ by using right $A$-modules rather than left
  $A$-modules, we obtain the same $rad A$.
] <cor:radical-left-right>

#proof[
  #source(89)The preceding theorem gives a left–right symmetric characterization
  of the radical.
]

A left ideal $N$ of $A$ is _nilpotent_ if there exists a positive integer $k$
such that
#idx("nilpotent")
$
  underbrace(N dot N dots.c N, k) = 0,
$
or equivalently, $x_1 dots.c x_k = 0$ for all ${x_i} in N$. An element $x in A$
is _nilpotent_ if $x^k = 0$ for some $k$. An element $e in A$ is _idempotent_ if
$e != 0$ and $e^2 = e$. Obviously, a nilpotent ideal cannot contain any
idempotent elements.
#idx("idempotent")

#theorem[
  Let $N$ be a nilpotent left ideal of $A$, and let $x in A$ be a non-nilpotent
  element such that $x^2 - x in N$. Then the left ideal $A x$ contains an
  idempotent $y$ such that $y - x in N$.
] <th:idempotent-modulo-nilpotent>

#proof[
  Let $N^k = 0$, and set $n_1 = x^2 - x in N$. If $n_1 = 0$, choose $y = x$, and
  we are done. If $n_1 != 0$, let
  $
    x_1 = x + n_1 - 2 x n_1 in A x.
  $
  Then $x$, $x_1$ and $n_1$ commute with each other, and hence if $x_1$ is
  nilpotent, so also is $x = x_1 - n_1 + 2 x n_1$, a contradiction. Thus $x_1$
  is a non-nilpotent element of $A x$, and direct calculation gives
  $
    x_1^2 - x_1 = 4 n_1^3 - 3 n_1^2.
  $
  The element $n_2 = x_1^2 - x_1$ is nilpotent, contains $n_1^2$ as factor, and
  commutes with $x_1$. Continuing in this manner, we may construct a sequence
  ${x_i}$ of non-nilpotent elements of $A x$, such that $n_1^(2^i)$ occurs as a
  factor in $x_i^2 - x_i$. If we choose $i$ so that $2^i >= k$, then we have
  $x_i^2 - x_i = 0$. Further, $x_i != 0$ since $x_i$ is non-nilpotent. Thus we
  may take $y = x_i$, the desired idempotent in $A x$ such that $y - x in N$.
]

#corollary[
  Let $L$ be a non-nilpotent left ideal in a left artinian ring $A$. Then $L$
  contains an idempotent element.
] <cor:idempotent-in-non-nilpotent>

#proof[
  Let $L_1$ be a minimal member of the (non-empty) set of non-nilpotent left
  ideals contained in $L$; then $L_1^2 subset L_1$, whence $L_1^2 = L_1$. Now
  let $I$ be minimal in the set of left ideals contained in $L_1$ such that
  $L_1 dot I != 0$, and choose $a in I$ so that $L_1 dot a != 0$. Then
  $L_1 dot L_1 a != 0$ and $L_1 a subset I$, whence $L_1 a = I$. Hence $a = x a$
  for some $x in L_1$, and thus $a = x^k a$ for all $k >= 0$. Therefore $I$
  contains the non-nilpotent element $x$.

  If we now set
  $
    N = {b in L_1 : b a = 0},
  $
  #source(90)then $x^2 - x in N$. Further, $L_1 a = I != 0$ so $N < L_1$. Then
  $N$ is nilpotent, by the way in which $L_1$ was chosen. Thus $A x$ contains an
  idempotent element by @th:idempotent-modulo-nilpotent, whence so does $L$,
  since $L supset L_1 supset A x$.
]

#theorem[
  If $A$ is left artinian, then $rad A$ is the largest nilpotent left ideal of
  $A$.
] <th:radical-largest-nilpotent>

#proof[
  If $L$ is a nilpotent left ideal, and $x in L$, then for all $a, b in A$ also
  $a x b$ is nilpotent; namely,
  $
    (a x b)^k = a x dot (b a x)^(k-1) dot b in L^k dot b = 0.
  $
  But then $1 - a x b in u(A)$, since
  $
    1 + a x b + (a x b)^2 + dots.c
  $
  is a two-sided inverse of $1 - a x b$. This proves that $L subset rad A$, by
  @th:radical-units.

  On the other hand, $rad A$ must itself be nilpotent; for, if not, then by
  @cor:idempotent-in-non-nilpotent $rad A$ contains an idempotent $e$. Hence
  $1 - e in u(A)$ by @th:radical-units, which is impossible since
  $(1 - e) e = 0$ but $e != 0$.
]

We may remark that if $A$ is left artinian, then $rad A$ is also the largest
nilpotent right ideal. For if $J$ is any nilpotent right ideal of $A$, then
$A J$ is a nilpotent two-sided ideal, whence $J subset A J subset rad A$.

Now we prove some easy properties of radicals.

#theorem[
  If $f: A -> B$ is an epimorphism of rings, then $f(rad A) subset rad B$. Hence
  $f$ induces an epimorphism $A slash rad A -> B slash rad B$.
] <th:radical-epimorphism>

#proof[
  Let $x in rad A$, $y = f(x)$, and let $b_1, b_2 in B$. Then there exist
  $a_1, a_2 in A$ such that $b_i = f(a_i)$, $i = 1, 2$. But
  $1 - a_1 x a_2 in u(A)$, whence $1 - b_1 y b_2 in u(B)$. Hence $y in rad B$,
  by @th:radical-units.
]

#theorem(title: [Nakayama's Lemma])[
  Let $M$ be a finitely generated left $A$-module such that $(rad A) M = M$.
  Then $M = 0$.
  #idx("Nakayama's Lemma", target: [@th:nakayama])
] <th:nakayama>

#proof[
  If $M != 0$, let $m_1, dots, m_k$ be a minimal set of generators of the left
  $A$-module $M$. Since $m_1 in M = (rad A) M$, we may write
  $
    m_1 = r_1 m_1 + dots.c + r_k m_k, quad r_i in rad A.
  $
  But then $1 - r_1 in u(A)$, so we can solve for $m_1$ in terms of
  $m_2, dots, m_k$, thereby reducing the number of generators of $M$.
]

#corollary[
  Let $M$ be a finitely generated left $A$-module, and $N$ a submodule such that
  #source(91)
  $
    N + (rad A) M = M.
  $
  Then $N = M$.
] <cor:nakayama-submodule>

#proof[
  The hypothesis implies that $M slash N$ is finitely generated, and
  $(rad A)(M slash N) = M slash N$. The result then follows from @th:nakayama.
]

#corollary[
  Every maximal two-sided ideal $J$ of $A$ contains $rad A$.
] <cor:maximal-ideal-contains-radical>

#proof[
  If $J supset.not rad A$, then $J + rad A$ is a two-sided ideal of $A$ properly
  containing $J$. Hence $J + rad A = A$, whence $J = A$ by applying
  @cor:nakayama-submodule with $N = J$, $M = A$.
]

=== Local rings <ss:local-rings>

The ring $A$ is _local_ (or _completely primary_) if $A$ has a unique maximal
left ideal. #idx("local ring")#idx("completely primary")

#theorem[
  The following are equivalent:
  + $A$ is local.
  + The set $S$ of non-units of $A$ is a left ideal of $A$.
  + $A slash rad A$ is a skewfield (that is, a ring whose nonzero elements form
    a multiplicative group).
] <th:local-ring-criteria>
#idx("skewfield")

#proof[
  Suppose first that $A$ is local, with $J$ its unique maximal left ideal, so of
  course $J subset S$. Since $rad A$ is the intersection of all maximal left
  ideals of $A$, we have $rad A = J$, and so $J$ is a two-sided ideal. We claim
  that $S = J$. For let $x in S$; if $A x != A$, then $A x$ lies in a maximal
  left ideal of $A$, whence $A x subset J$, so $x in J$. On the other hand, if
  $A x = A$ then for some $y in A$, $y x = 1$. Clearly $y in.not J$, otherwise,
  $1 = y x in rad A$. Hence $A y = A$, so there exists an element $z in A$ with
  $z y = 1$, and hence $z = x$. Thus $x in u(A)$, a contradiction. This proves
  that $S = J$, and shows also that each element of $A - J$ is a unit in $A$,
  whence $A slash rad A$ is a skewfield.

  Next, suppose that $S$ is a left ideal of $A$. Since every proper one-sided
  ideal of $A$ lies in $S$, it is clear that $S$ is the unique maximal left
  ideal (and also right ideal), so $A$ is local.

  Finally, suppose that $A slash rad A$ is a skewfield. Clearly
  $rad A subset S$, and we need only prove the reverse inclusion. If
  $x in A - rad A$, there exists $y in A$ such that $y x = 1 + n$, for some
  $n in rad A$. Hence $y x in u(A)$, and $x$ has a left inverse in $A$.
  Analogously, $x$ has a right inverse, whence $x in u(A)$. Thus
  $A - rad A subset u(A)$, so $S subset rad A$, as desired. This completes the
  proof.
]

#theorem[
  Let $R$ be a commutative local ring, with maximal ideal #source(
    92,
  )$P = rad R$, and residue class field $overline(R) = R slash P$. Let $A$ be an
  $R$-algebra, finitely generated as $R$-module, and let
  $phi: A -> overline(A) = A slash P A$ be the natural epimorphism of $A$ onto
  the finite dimensional $overline(R)$-algebra $overline(A)$. Then we have
  $
    P A subset phi^(-1) (rad overline(A)) = rad A,
  $
  and $(rad A)^t subset P A$ for some $t$. Further, $phi$ induces a ring
  isomorphism
  $
    A slash rad A tilde.equiv overline(A) slash rad overline(A).
  $
] <th:radical-local-algebra>

#proof[
  We show first that $rad A supset P A$. Let $M$ be any simple left $A$-module;
  then $M = A m$ for each nonzero $m in M$, whence $M$ is finitely generated as
  $R$-module. Now $P M$ is an $A$-submodule of $M$, hence is 0 or $M$. But
  $P M != M$, otherwise by Nakayama's Lemma we find that $M = 0$. Thus
  $P M = 0$, and so $P A$ annihilates every such $M$. Therefore
  $P A subset rad A$.

  By @th:radical-epimorphism, $phi$ induces an epimorphism
  $
    A slash rad A -> overline(A) slash rad overline(A).
  $
  On the other hand, there is an epimorphism
  $psi: overline(A) -> A slash rad A$, since $P A subset rad A$. By
  @th:quotient-by-radical-semisimple we have
  $psi(rad overline(A)) subset rad (A slash rad A) = 0$, and thus $psi$ induces
  an epimorphism $overline(A) slash rad overline(A) -> A slash rad A$. Both of
  these quotients are finite dimensional $overline(R)$-algebras, and thus are
  isomorphic. This shows that $rad A = phi^(-1) (rad overline(A))$, as well.

  Next, $rad overline(A)$ is a nilpotent ideal of the left (and right) artinian
  ring $overline(A)$, by @th:radical-largest-nilpotent, and hence
  $(rad overline(A))^t = 0$ for some $t$. Thus $phi{(rad A)^t} = 0$, whence
  $(rad A)^t subset P A$, as claimed.
]

We shall need some standard results on completions of a commutative local ring
$R$, and of modules over such a ring. Suppose first that
$X = dsum_(i=1)^k R x_i$ is a free $R$-module, and let $P$ denote the maximal
ideal of $R$. We define a _$P$-adic topology_ on $X$, by taking as basis for the
neighborhoods of a point $x in X$ the sets ${x + P^m X : m = 0, 1, 2, dots}$.
Given a sequence ${y_n}$ from $X$, we may write
#idx("$P$-adic topology")
$
  y_n = r_n^((1)) x_1 + dots.c + r_n^((k)) x_k, quad r_n^((i)) in R.
$
Then ${y_n}$ is a Cauchy sequence in $X$ if and only if, for each $i$,
${r_n^((i))}$ is a Cauchy sequence in $R$. Further, ${y_n}$ converges if and
only if each ${r_n^((i))}$ converges, and we have
$
  lim_(n -> infinity) sum r_n^((i)) x_i = sum (lim_(n -> infinity) r_n^((i)))
  x_i.
$
Thus if $R$ is complete in the $P$-adic topology, then so is $X$. When $R$ is
not complete, we may form its $P$-adic completion $hat(R)$. Then
$hat(R) times.o_R X$ is a free #source(93)$hat(R)$-module, and can be
topologized as above. If $hat(X)$ denotes the $P$-adic completion of $X$, the
above discussion shows that there is an $hat(R)$-isomorphism
$
  hat(X) tilde.equiv hat(R) times.o_R X,
$
and that this is a topological isomorphism.

The following generalization of the above holds true, and we refer the reader to
Bourbaki [@bib:Bourbaki1961b, Ch.~3] or Matsumura [@bib:Matsumura1970] for
proofs:

#theorem[
  Let $R$ be a commutative noetherian local ring, with maximal ideal $P$, and
  let $hat(R)$ be the $P$-adic completion of $R$. Let $X$ be a finitely
  generated $R$-module, and let $hat(X)$ be the completion of $X$ relative to
  the $P$-adic topology on $X$, defined by taking ${x + P^m X}$ as basis for the
  neighborhoods of $x in X$. Let $hat(R) times.o_R X$ be topologized by taking
  ${xi + P^m (hat(R) times.o X)}$ as basis for the neighborhoods of
  $xi in hat(R) times.o X$. Then there is a topological $hat(R)$-isomorphism
  $
    hat(X) tilde.equiv hat(R) times.o_R X,
  $
  and $hat(X)$ is a complete Hausdorff space relative to its $P$-adic topology.
] <th:completion-of-module>

#corollary[
  Let $R$ be a complete commutative noetherian local ring, and let $A$ be an
  $R$-algebra which is finitely generated as $R$-module. Then $A$ is a complete
  Hausdorff space relative to the $P$-adic topology on $A$.
] <cor:algebra-complete>

For the most part, we shall be dealing with the case where $R$ is a complete
discrete valuation ring, and $A$ is an $R$-order. In this case, $A$ is of course
$R$-free, and we need not use @th:completion-of-module and @cor:algebra-complete
in their full generality.

=== Lifting idempotents <ss:lifting-idempotents>

We shall discuss here the relationship between idempotents in a ring $A$, and
idempotents in a factor ring $overline(A) = A slash N$, where $N$ is a two-sided
ideal of $A$ contained in $rad A$. To begin with, suppose that there is a direct
sum decomposition
$
  A = L_1 plus.o dots.c plus.o L_k,
$
where each $L_i$ is an indecomposable left ideal of $A$. We may write
$
  1 = e_1 + dots.c + e_k, quad e_i in L_i.
$
For each $x in L_i$, we obtain $x = sum x e_i$, whence $x e_i = x$ and
$x e_j = 0$ for $j != i$. This gives
$
  e_i^2 = e_i, quad e_i e_j = 0 thin (j != i), quad L_i = A e_i.
$
Thus each $e_i$ is idempotent, and we call ${e_1, dots, e_k}$ a full set of
_orthogonal #idx("orthogonal idempotents")#source(94)idempotents_ in $A$.
Further, each $e_i$ is _primitive_, that is, $e_i$ cannot be expressed as a sum
$e' + e''$ of orthogonal idempotents; for if $e_i = e' + e''$, then
$L_i = A e' plus.o A e''$ gives a decomposition of $L_i$. #idx(
  "orthogonal idempotents",
)#idx("primitive idempotent")

We have thus shown that there is a one-to-one correspondence between
decompositions of $A$ into direct sums of indecomposable left ideals, and
decompositions of $1_A$ into a sum of primitive orthogonal idempotents.

Now let $overline(A) = A slash N$, where $N$ is a two-sided ideal of $A$ such
that $N subset rad A$, and let $a in A$ have image $overline(a) in overline(A)$.
If $e in A$ is idempotent, then $overline(e)$ is an idempotent in $overline(A)$;
indeed, $e^2 = e$ implies that $overline(e)^2 = overline(e)$, while if
$overline(e) = 0$ then $e in rad A$, an impossibility (see proof of
@th:radical-largest-nilpotent). Thus each decomposition $1 = sum e_i$ into
orthogonal idempotents in $A$ gives a corresponding such decomposition
$overline(1) = sum overline(e)_i$ in $overline(A)$. In general, however, it may
happen that $e_i$ is primitive but $overline(e)_i$ is not. Our aim here is to
show that under suitable hypotheses, $overline(e)_i$ is primitive whenever $e_i$
is primitive, and indeed, that every decomposition $overline(1) = sum epsilon_i$
into a sum of primitive orthogonal idempotents "lifts" to a decomposition
$1 = sum e_i$ into primitive orthogonal idempotents, such that
$overline(e)_i = epsilon_i$ for each $i$.

Given any two-sided ideal $N$ of $A$, we may give $A$ the _$N$-adic topology_ by
taking as basis for the open neighbourhoods of an element $a in A$ the sets
${a + N^r : r = 0, 1, dots}$. We call $A$ _complete_ in the $N$-adic topology if
each Cauchy sequence (relative to this topology) converges to an element of $A$.
If $N subset rad A$, there are two obvious cases where $A$ is necessarily
complete in the $N$-adic topology: #idx("$N$-adic topology")#idx(
  "complete (in $N$-adic topology)",
)
+ if $A$ is a left artinian ring, then $N$ is a nilpotent ideal by
  @th:radical-largest-nilpotent, and hence any Cauchy sequence from $A$,
  relative to the $N$-adic topology, is constant from some point on;
+ if $A$ is an $R$-algebra, finitely generated as $R$-module, where $R$ is a
  complete noetherian local ring with maximal ideal $P$, then by
  @th:radical-local-algebra we have
  $
    N^t subset (rad A)^t subset P A
  $
  for some $t$. Hence any Cauchy sequence (from $A$) relative to the $N$-adic
  topology is also a Cauchy sequence in the $P$-adic topology and thus converges
  by @cor:algebra-complete.

For the remainder of this section, we assume that $A$ is complete in the
$N$-adic topology.

#theorem[
  Each idempotent $epsilon in overline(A)$ can be lifted to an idempotent
  $e in A$, that is, $overline(e) = epsilon$. If $e_1$, $e_2$ are idempotents of
  $A$, then $A e_1 tilde.equiv A e_2$ as left $A$-modules if and only if
  $overline(A) overline(e)_1 tilde.equiv overline(A) overline(e)_2$ as left
  $overline(A)$-modules.
  #idx("lifting idempotents", target: [@th:lifting-idempotents])
] <th:lifting-idempotents>

#proof[
  We examine the proof of @th:idempotent-modulo-nilpotent. Given an idempotent
  $epsilon in overline(A)$, choose any $x_1 in A$ with
  $overline(x)_1 = epsilon$. Then $n_1 = x_1^2 - x_1 in N$. Once $x_i$ and $n_i$
  are chosen, let
  $
    x_(i+1) = x_i + n_i - 2 x_i n_i, quad n_(i+1) = x_(i+1)^2 - x_(i+1).
  $
  #source(95)Then $n_i in N^(2^i)$, and so ${x_i}$ is a Cauchy sequence in the
  $N$-adic topology of $A$. Let $e = lim_(i -> infinity) x_i in A$. Then
  $
    e^2 - e = lim n_i = 0,
  $
  and furthermore $overline(e) = overline(x)_1 = epsilon$, so $e != 0$, and $e$
  is the desired idempotent in $A$.

  Now let $e_1, e_2 in A$ be idempotent. Any isomorphism
  $A e_1 tilde.equiv A e_2$ carries $N e_1$ onto $N e_2$, and induces an
  isomorphism $overline(A) overline(e)_1 tilde.equiv overline(A) overline(e)_2$.
  Conversely, let $overline(f): overline(A) overline(e)_1 tilde.equiv
  overline(A) overline(e)_2$, and let $overline(g) = overline(f)^(-1)$. Then in
  the diagram
  $
    #lifted-isomorphism
  $
  the vertical arrows are epic. Since $A = A e_i plus.o A(1 - e_i)$, each
  $A e_i$ is $A$-projective. Hence we can find $A$-homomorphisms $f$, $g$
  lifting $overline(f)$, $overline(g)$, respectively. We claim that $f$ is an
  isomorphism, and need only show that $theta = g dot f$ is an automorphism of
  $A e_1$ (for then, by symmetry, $f dot g$ is an automorphism of $A e_2$).
  Clearly $theta$ lifts $overline(g) dot overline(f)$, and hence
  $(theta - 1) A e_1 subset N e_1$. Let $xi = 1 - theta$; then
  $xi^k dot A e_1 subset N^k e_1$; thus $1 + xi + xi^2 + dots.c$ is a well
  defined endomorphism of $A e_1$, and is a two-sided inverse of $1 - xi$. Since
  $1 - xi = theta$, this shows that $theta$ is an $A$-automorphism of $A e_1$,
  as claimed. This completes the proof.#footnote[For more general theorems of
    this type, see Azumaya [@bib:Azumaya1951, Th.~24].]
]

#theorem[
  Let $overline(1) = epsilon_1 + dots.c + epsilon_n$ be a decomposition of
  $overline(1)$ into orthogonal idempotents in $overline(A)$. Then there exist
  orthogonal idempotents $e_1, dots, e_n in A$ such that
  $
    1 = e_1 + dots.c + e_n, quad overline(e)_i = epsilon_i.
  $
  #idx("lifting idempotents", target: [@th:lifting-orthogonal-idempotents])
] <th:lifting-orthogonal-idempotents>

#proof[
  We proceed by induction on $n$, the result being trivial when $n = 1$. Assume
  that $n > 1$ and that the result holds at $n - 1$. Set
  $delta = epsilon_(n-1) + epsilon_n$, so now
  $overline(1) = epsilon_1 + dots.c + epsilon_(n-2) + delta$ is an orthogonal
  decomposition. By the induction hypothesis there exists an orthogonal
  decomposition
  $
    1 = e_1 + dots.c + e_(n-2) + e, quad
    overline(e)_1 = epsilon_1, dots, overline(e)_(n-2) = epsilon_(n-2), quad
    overline(e) = delta.
  $
  Choose $a in A$ such that $overline(a) = epsilon_(n-1)$, and set $b = e a e$.
  Then $overline(b) = delta dot epsilon_(n-1) dot delta = epsilon_(n-1)$, and
  $e_i b = b e_i = 0$, $1 <= i <= n - 2$. In the proof of
  @th:lifting-idempotents, we take $x_1 = b$. Then the sequence ${x_i}$
  converges to an idempotent $e_(n-1) in A$ such that
  $overline(e)_(n-1) = epsilon_(n-1)$, and $e_i e_(n-1) = e_(n-1) e_i = 0$,
  $1 <= i <= n - 2$. Finally, set #source(96)$e_n = e - e_(n-1)$; then
  $1 = e_1 + dots.c + e_n$ is the desired orthogonal decomposition in $A$ such
  that $overline(e)_i = epsilon_i$ for $1 <= i <= n$.
]

#corollary[
  An idempotent $e in A$ is primitive if and only if its image
  $overline(e) in overline(A)$ is primitive.
] <cor:primitive-lifts>

#proof[
  If $e$ is imprimitive, there is an orthogonal decomposition $e = e_1 + e_2$
  into idempotents $e_1, e_2 in A$. Then
  $overline(e) = overline(e)_1 + overline(e)_2$ is an orthogonal decomposition
  of $overline(e)$. Conversely, let $overline(e) = epsilon_1 + epsilon_2$ be an
  orthogonal decomposition into idempotents of $overline(A)$. The proof of
  @th:lifting-orthogonal-idempotents shows that there exist orthogonal
  idempotents $e_1, e_2 in A$ such that $overline(e)_1 = epsilon_1$,
  $overline(e)_2 = epsilon_2$, and $e = e_1 + e_2$. This completes the proof.
]

#theorem[
  Let $A$ be a left artinian ring, and let $overline(A) = A slash rad A$. Let
  $1 = e_1 + dots.c + e_n$ be a decomposition of $1 in A$ into orthogonal
  primitive idempotents in $A$. Then
  $
    A = A e_1 plus.o dots.c plus.o A e_n
  $
  is a decomposition of $A$ into indecomposable left ideals of $A$, and
  $
    overline(A) = overline(A) overline(e)_1 plus.o dots.c plus.o
    overline(A) overline(e)_n
  $
  is a decomposition of $overline(A)$ into minimal left ideals. Further,
  $A e_i tilde.equiv A e_j$ if and only if
  $overline(A) overline(e)_i tilde.equiv overline(A) overline(e)_j$.
] <th:artinian-decomposition>

#proof[
  Since $A$ is left artinian, it can be expressed as a finite direct sum
  $dsum_1^n L_i$ of indecomposable left ideals of $A$. Writing $1 = sum e_i$,
  $e_i in L_i$, we obtain a decomposition of 1 into orthogonal primitive
  idempotents. Then $overline(1) = sum overline(e)_i$ is such a decomposition in
  $overline(A)$, and so each $overline(A) overline(e)_i$ is an indecomposable
  left ideal of $overline(A)$. But $overline(A)$ is a semisimple artinian ring,
  so (see @th:semisimple-artinian-structure) every indecomposable left ideal of
  $overline(A)$ is a minimal left ideal. The last statement in the theorem has
  already been established in @th:lifting-idempotents, so the proof is
  completed.
]

#corollary[
  Let $A$ be an $R$-algebra, finitely generated as $R$-module, where $R$ is a
  complete noetherian commutative local ring. Then the assertions in the
  preceding theorem remain valid for this case.
] <cor:complete-local-decomposition>

#proof[
  In the proof of @th:artinian-decomposition, we used the hypothesis there that
  $A$ be left artinian, in order to guarantee that
  + $A$ is expressible as a finite direct sum of indecomposable left ideals, and
  + $A slash rad A$ is a semisimple artinian ring.
  However, both of these remain valid under the hypotheses of the present
  #source(97)corollary. The first is true, since in the present case $A$ is a
  left noetherian ring. The second holds true, by virtue of
  @th:radical-local-algebra. Thus the proof of @th:artinian-decomposition
  applies equally well in this case, and the corollary is established.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $J$ be a two-sided ideal of a ring $A$, such that $A slash J$ is
  semisimple. Prove that $J supset rad A$.
  #hint[@exc:semisimple-quotient-contains-radical][By @th:radical-epimorphism,
    $(J + rad A) slash J subset rad (A slash J) = 0$.]
  <hint:semisimple-quotient-contains-radical>
] <exc:semisimple-quotient-contains-radical>

#exercise[
  Let $x in A$ map onto $overline(x) in A slash rad A$. Show that $x in u(A)$ if
  and only if $overline(x) in u(A slash rad A)$.
] <exc:units-modulo-radical>

#exercise[
  Keep the notation and hypotheses of @th:radical-local-algebra, and let $J$ be
  any two-sided ideal of $A$ such that $J^m subset P A$. Show that
  $J subset rad A$. #hint[@exc:ideal-in-radical][$phi(J)$ is a nilpotent ideal
    in the artinian ring $overline(A)$, whence $phi(J) subset rad overline(A)$,
    so $J subset phi^(-1) (rad overline(A)) = rad A$.] <hint:ideal-in-radical>
] <exc:ideal-in-radical>

In Exercises~@exc:local-iff-no-idempotents–@exc:summand-of-sum below, let $R$ be
a complete noetherian commutative local ring, and let $A$ be an $R$-algebra
which is finitely generated as $R$-module. We include here the special case
where $R$ is a field, and ${0}$ is its maximal ideal.

#exercise[
  Prove that $A$ is a local ring if and only if 1 is the only idempotent in $A$.
  #hint[@exc:local-iff-no-idempotents][Let $A$ be local, and let $e in A$ be
    idempotent, $e != 1$. Since $e(1 - e) = 0$, both $e$ and $1 - e$ are
    non-units, whence so is their sum; this is a contradiction. Conversely, if
    $A$ is not local, then $A slash rad A$ is not a skewfield. If $P = rad R$,
    then by @th:radical-local-algebra we know that $A slash rad A$ is a finite
    dimensional semisimple $(R slash P)$-algebra. Hence by
    §~@sec:semisimple-rings, $A slash rad A$ contains an idempotent other
    than 1. Therefore $A$ contains an idempotent different from 1, by
    @th:lifting-idempotents.] <hint:local-iff-no-idempotents>
] <exc:local-iff-no-idempotents>

#exercise[
  An _indecomposable_ left $A$-module is a nonzero left $A$-module which is not
  expressible as a direct sum of non-trivial submodules. Let $M$ be a nonzero
  finitely generated left $A$-module, and set $E = Hom_A (M, M)$. Show that $E$
  is an $R$-algebra which is finitely generated as $R$-module. Using
  Exercise~@exc:local-iff-no-idempotents, deduce that $M$ is indecomposable as
  $A$-module if and only if $E$ is a local ring.
  #idx("indecomposable module")
  #hint[@exc:indecomposable-local-endomorphisms][Given a non-trivial
    decomposition $M = M_1 plus.o M_2$ into $A$-submodules, let $pi_1: M -> M_1$
    be the corresponding projection of $M$ onto $M_1$. Then $pi_1 in E$ is an
    idempotent, and $pi_1 != 1$. Conversely, if $e in E$ is an idempotent
    different from 1, then $M = e M plus.o (1 - e) M$ gives a decomposition of
    $M$.] <hint:indecomposable-local-endomorphisms>
] <exc:indecomposable-local-endomorphisms>

#exercise[
  Prove the *Krull–Schmidt Theorem*: Every finitely generated left $A$-module
  $M$ is expressible as a finite direct sum of indecomposable modules, and these
  direct summands are uniquely determined by $M$, up to $A$-isomorphism and
  order of occurrence.
  #idx("Krull–Schmidt Theorem")
  #hint[@exc:krull-schmidt][Since $M$ is finitely generated over the commutative
    noetherian ring $R$, $M$ is itself a noetherian module. The process of
    decomposing $M$ into direct summands must therefore terminate.

    Now let
    $
      M = M_1 plus.o dots.c plus.o M_t = N_1 plus.o dots.c plus.o N_u,
    $
    where the ${M_i}$ and ${N_j}$ are indecomposable. Let $mu_i: M -> M_i$,
    $nu_j: M -> N_j$, be the projections associated with these decompositions.
    Restrict the operators in the equation $mu_1 = sum mu_1 nu_j$ to $M_1$,
    getting the relation $1 = sum mu_1 nu_j$ in the local ring
    $Hom_A (M_1, M_1)$. Hence some $mu_1 nu_j$ must be a unit in this ring, that
    is, must be an automorphism of $M_1$. If (say) $mu_1 nu_1$ is an
    automorphism $phi$ of $M_1$, then in the diagram
    #source(98)
    $
      #arrow-pair($M_1$, $N_1,$, $nu_1$, $phi^(-1) mu_1$)
    $
    $nu_1$ is monic and $phi^(-1) mu_1 dot nu_1$ is the identity on $M_1$. Hence
    there is a splitting $N_1 tilde.equiv M_1 plus.o ker phi^(-1) mu_1$, and
    therefore $N_1 tilde.equiv M_1$. Thus both $nu_1$ and $mu_1$ are
    isomorphisms.

    Next verify that the sum
    $
      M' = N_1 plus.o M_2 plus.o dots.c plus.o M_t
    $
    is direct. Then show that $M' = M$, since for each $x in N_1$,
    $
      mu_1 x = x - mu_2 x - dots.c - mu_t x in M',
    $
    and thus $M_1 = mu_1 (N_1) subset M'$. Prove next that the map
    $
      p = nu_1 mu_1 + mu_2 + dots.c + mu_t
    $
    defines an $A$-isomorphism of $M$ onto $M'$, carrying $M_1$ onto $N_1$.
    Therefore $p$ induces an $A$-isomorphism
    $
      M_2 plus.o dots.c plus.o M_t tilde.equiv M slash N_1 tilde.equiv
      N_2 plus.o dots.c plus.o N_u.
    $
    An induction argument completes the proof.] <hint:krull-schmidt>
] <exc:krull-schmidt>

#exercise[
  Let $L$, $M$, $N$ be finitely generated left $A$-modules such that
  $
    L dotplus M tilde.equiv L dotplus N.
  $
  Prove that $M tilde.equiv N$. #hint[@exc:cancellation][Express $L$, $M$, $N$
    as direct sums of indecomposable modules, and then use the Krull–Schmidt
    Theorem proved above.] <hint:cancellation>
] <exc:cancellation>

#exercise[
  Let ${M_1, dots, M_t}$ be finitely generated indecomposable left $A$-modules,
  and let $L$ be a left $A$-module which is isomorphic to a direct summand of
  $M_1 dotplus dots.c dotplus M_t$. Show that
  $
    L tilde.equiv M_(i_1) dotplus dots.c dotplus M_(i_r),
  $
  where ${i_1, dots, i_r}$ is some subset of ${1, dots, t}$.
  #hint[@exc:summand-of-sum][The hypothesis implies that
    $dsum_(i=1)^t M_i tilde.equiv L dotplus L'$, where both $L$ and $L'$ are
    finitely generated left $A$-modules. Now express $L$ and $L'$ as direct sums
    of indecomposable modules, and then use the Krull–Schmidt Theorem.]
  <hint:summand-of-sum>
] <exc:summand-of-sum>

#exercise[
  Let $A$ be an $R$-algebra as in @cor:complete-local-decomposition, and let $P$
  be the unique maximal ideal of $R$. Assume that $P$ does not annihilate any
  nonzero $R$-submodule of $A$. Let $J = rad A$, and set
  $overline(A) = A slash J$. Show that _every_ simple left $overline(A)$-module
  occurs as a direct summand of the left $overline(A)$-module $J slash J^2$.
  #hint[@exc:simple-in-radical-layer][Assume the result false. By
    §~@sec:semisimple-rings, there is a central idempotent $epsilon$ in the
    semisimple artinian ring $overline(A)$ such that
    $epsilon dot (J slash J^2) = 0$. By @th:lifting-idempotents there exists an
    idempotent $e in A$ mapping onto $epsilon$. Then $e J subset J^2$, whence
    multiplying by $e$ we obtain $e J = e J^2 = e J dot J$. Therefore $e J = 0$
    by Nakayama's Lemma. But $J supset P A$ by @th:radical-local-algebra, and so
    $P dot e A = 0$. This gives $e A = 0$, so $e = 0$ and $epsilon = 0$, a
    contradiction.]
  <hint:simple-in-radical-layer>
] <exc:simple-in-radical-layer>
