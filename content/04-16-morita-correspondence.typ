#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/01-02-homological-algebra.typ": square
#import "diagrams/04-15-progenerators.typ": arrow-pair

== Morita correspondence <sec:morita-correspondence>

Let $M_Delta$ be a nonzero right $Delta$-module, and set
$
  Lambda = Hom_Delta (M, M), quad M^* = Hom_Delta (M, Delta).
$ <eq:derived-context-rings>
Let $Lambda$ act on the left on $M$, so there is a bimodule structure
$lmodule(Lambda, M)_Delta$. By definition,
$
  M^* = Hom_Delta (lmodule(Lambda, M)_Delta, lmodule(Delta, Delta)_Delta),
$
the set of all _right_ $Delta$-homomorphisms from $M$ to $Delta$. The left
action of $Delta$ on the bimodule $lmodule(Delta, Delta)_Delta$ enables us to
make $M^*$ into a left $Delta$-module. The left action of $Lambda$ on the
bimodule $lmodule(Lambda, M)_Delta$ likewise makes $M^*$ a _right_
$Lambda$-module (see §~@sec:homological-algebra). It is easily verified that
$M^*$ is a bimodule $lmodule(Delta, M^*)_Lambda$.

We define a map
$
  mu : M times.o_Delta M^* -> Lambda, quad m times.o f -> (m, f), quad
  "where" (m, f) m' = m (f m')
$ <eq:derived-context-mu>
for $m, m' in M$, $f in M^*$. Likewise, let
$
  tau : M^* times.o_Lambda M -> Delta, quad f times.o m' -> [f, m'], quad
  "where" [f, m'] = f m'.
$ <eq:derived-context-tau>
It is easily checked that $mu$ and $tau$ are well defined, $mu$ is a two-sided
$Lambda$-homomorphism, and $tau$ a two-sided $Delta$-homomorphism. Further, one
obtains
$
  (m, f) m' = m [f, m'], quad g (m, f) = [g, m] f,
$ <eq:derived-context-identities>
for $m, m' in M$, $f, g in M^*$. Finally, we note that
$
  im tau = "trace" M_Delta,
$ <eq:derived-context-trace>
where "trace" is defined as in @eq:trace-ideal.

#definition[
  #source(171)A _Morita context_ consists of a pair of bimodules
  $lmodule(Lambda, M)_Delta$, $lmodule(Delta, N)_Lambda$ relative to rings
  $Delta$, $Lambda$, and bimodule maps
  $
    mu : M times.o_Delta N -> Lambda, quad tau : N times.o_Lambda M -> Delta,
  $
  given symbolically by $mu(m times.o n) = (m, n)$, $tau(n times.o m) = [n, m]$,
  interrelated by the formulas
  $
    (m, n) m' = m [n, m'], quad n (m, n') = [n, m] n',
  $
  for all $m, m' in M$, $n, n' in N$. If both $mu$ and $tau$ are isomorphisms,
  we call the rings $Delta$, $Lambda$ _Morita equivalent_. #idx(
    "Morita context",
  )#idx("Morita equivalence")
] <def:morita-context>

We have just seen how to construct a Morita context by starting with $M_Delta$,
and defining $Lambda$, $M^*$ by @eq:derived-context-rings. We call it the Morita
context _derived_ from the right $Delta$-module $M$. We now proceed to
investigate this derived context more fully, keeping the notation of
@eq:derived-context-rings–@eq:derived-context-trace. #idx(
  "derived Morita context",
)#idx("Morita context", "derived")

#theorem[
  Let $M$ be a nonzero right $Delta$-module, and let
  $Lambda = Hom_Delta (M, M)$. Let
  $
     mu & : M times.o_Delta Hom_Delta (M, Delta) -> Hom_Delta (M, M), \
    tau & : Hom_Delta (M, Delta) times.o_Lambda M -> Delta,
  $
  be the maps defined in @eq:derived-context-mu and @eq:derived-context-tau.
  Then $mu$ is epic if and only if $M$ is a finitely generated projective right
  $Delta$-module; in this case, $mu$ is also monic.

  On the other hand, $tau$ is epic if and only if $M$ is a generator of the
  category $cal(M)_Delta$; in this case, $tau$ is also monic.

  Finally, $mu$ is epic if and only if $1_Lambda in im mu$, and $tau$ is epic if
  and only if $1_Delta in im tau$.
] <th:derived-context-epic>

#proof[
  The last statement in the theorem is obvious, since $im mu$ is a two-sided
  ideal in $Lambda$, and $im tau$ a two-sided ideal in $Delta$.

  The identity map $1_M$ on $M$ is the identity element $1_Lambda$. Hence if
  $mu$ is epic, we may write
  $
    1_M = sum_(i=1)^r (m_i, f_i), quad m_i in M, quad
    f_i in Hom_Delta (M, Delta).
  $
  Define right $Delta$-homomorphisms $Delta^((r)) lrmaps(alpha, beta) M$ by
  $
    alpha(a_1, dots, a_r) = sum_1^r m_i a_i, quad
    beta(m) = (f_1 m, dots, f_r m).
  $
  It is easily seen that $alpha beta = 1_M$, whence $M | Delta^((r))$, and thus
  $M_Delta$ is finitely generated and projective. The argument can be reversed,
  and thus $mu$ is epic if and only if $M_Delta$ is finitely generated and
  projective.

  Next, $im tau = "trace" M_Delta$. Hence by @cor:generator-trace-ideal, $tau$
  is epic if and only if $M$ is a #source(172)generator for $cal(M)_Delta$.
  Finally, $mu$ epic implies $mu$ monic, by
  Exercise~@exc:morita-epic-implies-monic, and likewise for $tau$. This
  completes the proof.
]

The same argument shows

#corollary[
  For any Morita context @def:morita-context, we have
  $
    1_Lambda in im mu & ==> mu "epic" ==> mu "monic", \
    1_Delta in im tau & ==> tau "epic" ==> tau "monic".
  $
] <cor:morita-context-epic>

Recall that $M_Delta$ is a _progenerator_ of $cal(M)_Delta$ if $M$ is a finitely
generated projective $Delta$-module which is a generator of the category
$cal(M)_Delta$. The preceding results give at once

#corollary(major: true)[
  The module $M_Delta$ is a progenerator of $cal(M)_Delta$ if and only if both
  of the maps $mu, tau$ in @th:derived-context-epic are isomorphisms. If
  $M_Delta$ is a progenerator, then the Morita context derived from $M$ gives a
  Morita equivalence between the rings $Delta$ and $Hom_Delta (M, M)$.
] <cor:progenerator-morita-equivalence>

#remark(numbered: false)[
  Let $M_Delta$ be a progenerator of $cal(M)_Delta$. Then $M$ is a projective
  object in the category $cal(M)_Delta$, and by @cor:progenerator-equivalence
  there is an equivalence of categories
  $
    Hom_Delta (M, dot) : cal(M)_Delta -> cal(M)_Lambda,
  $ <eq:morita-hom-equivalence>
  where $Lambda = Hom_Delta (M, M)$, and $M$ is viewed as a bimodule
  $lmodule(Lambda, M)_Delta$. It is sometimes useful to exhibit this category
  equivalence in terms of tensor products, rather than $Hom$. Define $M^*$ as in
  @eq:derived-context-rings; by Exercise~@exc:tensor-dual-projective, there is
  an isomorphism
  $
    Hom_Delta (M, L) tilde.equiv L times.o_Delta M^*, quad L in cal(M)_Delta,
  $
  and it is easily verified that this is a right $Lambda$-isomorphism which is
  natural in $L$. In other words, there is an equivalence of functors
  $
    Hom_Delta (M, dot) tilde dot times.o_Delta M^*.
  $ <eq:hom-tensor-dual-equivalence>
  (This also follows from Exercise~@exc:hom-as-tensor-with-dual.) Hence the
  equivalence in @eq:morita-hom-equivalence can also be given as
  $
    dot times.o_Delta M^* : cal(M)_Delta -> cal(M)_Lambda.
  $
]

We shall show below that every Morita equivalence of rings $Delta, Lambda$ is
obtained in the manner described above, by means of the Morita context derived
from a progenerator $M_Delta$ of category $cal(M)_Delta$. As a first step in
establishing this fact, let us start with an arbitrary Morita context
@def:morita-context, not necessarily derived from a $Delta$-module $M$, and let
us see what conclusions may be drawn if we assume that $mu$ is epic.

#theorem[
  #source(173)Suppose that the map $mu$ occurring in the Morita context
  @def:morita-context is epic. Then both $M_Delta$ and $lmodule(Delta, N)$ are
  finitely generated projective modules, and $Lambda$ acts
  faithfully#footnote[This means that for $lambda in Lambda$, if $N lambda = 0$
    then $lambda = 0$.] on $N$. Furthermore,
  $
    M tilde.equiv Hom_Delta (N, Delta), quad
    Lambda tilde.equiv Hom_Delta (N, N).
  $
  The first of these is a $(Lambda, Delta)$-bimodule isomorphism, and the second
  is an isomorphism as rings of right operators on $N$.
] <th:mu-epic>

#proof[
  Let us form the Morita context derived from $lmodule(Delta, N)$, by setting
  $
    Lambda' = Hom_Delta (N, N), quad N^* = Hom_Delta (N, Delta).
  $
  Then $Lambda'$ is a ring, and there are bimodule structures
  $lmodule(Delta, N)_(Lambda')$, $lmodule(Lambda', N^*)_Delta$, and bimodule
  homomorphisms
  $
    mu' & : N^* times.o_Delta N -> Lambda', quad
    && f times.o n -> {f, n}, \
    tau' & : N times.o_(Lambda') N^* -> Delta, quad
    && n times.o f -> chevron.l n, f chevron.r = f(n),
  $
  where
  $
    n_1 {f, n} = chevron.l n_1, f chevron.r n, quad
    {f, n} g = f chevron.l n, g chevron.r.
  $

  We may now define a right $Delta$-homomorphism $psi$ by
  $
    psi : M -> N^*, quad m -> [dot, m],
  $
  where we use $( , )$ and $[ , ]$ for the maps $mu$, $tau$ occurring in
  @def:morita-context. Also define a ring homomorphism
  $
    phi : Lambda -> Lambda', quad lambda -> lambda_R,
  $
  where $lambda_R$ is right multiplication by $lambda$ on $N$. Let us verify
  that the following diagram is commutative:
  $
    #square(
      $M times.o_Delta N$,
      $N^* times.o_Delta N$,
      $Lambda$,
      $Lambda'.$,
      $psi times.o 1$,
      $mu$,
      $mu'$,
      $phi$,
    )
  $ <eq:mu-epic-square>
  To prove equality of two elements of $Lambda'$, we compute their action on an
  arbitrary element $n' in N$. We have
  $
    n' {(phi mu) dot (m times.o n)} = n' dot (m, n) = [n', m] n,
  $
  #source(174)whereas
  $
    n' dot {(mu' (psi times.o 1)) dot (m times.o n)}
    & = n' dot {mu' (psi m times.o n)} = n' dot {psi m, n} \
    & = chevron.l n', psi m chevron.r dot n = {(psi m) n'} dot n
    = [n', m] dot n.
  $
  This shows that @eq:mu-epic-square is commutative.

  Up to this point, we have not used our hypothesis that $mu$ is epic. Under
  this hypothesis, we know from @cor:morita-context-epic that $mu$ is in fact an
  isomorphism. We shall show that the other maps $phi$, $mu'$ and
  $psi times.o 1$ in @eq:mu-epic-square are also isomorphisms. We begin by
  proving that $psi$ itself is an isomorphism. Choose $z in M times.o N$ so that
  $mu(z) = 1_Lambda$; then
  $
    z = sum m_i times.o n_i, quad 1_Lambda = sum (m_i, n_i).
  $
  If $m in ker psi$, then $[N, m] = 0$, whence
  $
    m = sum (m_i, n_i) m = sum m_i [n_i, m] = 0,
  $
  and thus $psi$ is monic. To prove $psi$ epic, let $f in N^*$ and set
  $
    m = sum m_i dot f(n_i).
  $
  We show that $psi(m) = f$ by checking that for each $n in N$,
  ${psi(m)} n = f(n)$. We have
  $
    {psi(m)} n = [n, sum m_i dot f(n_i)] = sum [n, m_i] f(n_i).
  $
  But $f$ is a $Delta$-homomorphism, and $[n, m_i] in Delta$, whence
  $
    {psi(m)} n = f(sum [n, m_i] n_i) = f(sum n (m_i, n_i)) = f(n).
  $
  This completes the verification that $psi$ is an isomorphism. It follows at
  once that $psi times.o 1$ is also an isomorphism.

  Now we note that
  $
    1_(Lambda') = phi mu(z) = mu' {(psi times.o 1) z},
  $
  whence by @cor:morita-context-epic $mu'$ is an isomorphism. Since
  @eq:mu-epic-square commutes, it follows that $phi$ is an isomorphism, as
  claimed. This in turn implies that $Lambda$ acts faithfully on $N$.

  Finally, since $mu'$ is epic, it follows by @th:derived-context-epic that $N$
  is a finitely generated projective left $Delta$-module. But then $N^*$ is a
  finitely generated projective right $Delta$-module, since
  $(lmodule(Delta, Delta))^* = Delta_Delta$. We have shown above that
  $M tilde.equiv N^*$, whence we may conclude that $M_Delta$ is finitely
  generated and projective. This completes the proof.
]

We called the rings $Delta, Lambda$ _Morita equivalent_ if there exists a Morita
context @def:morita-context in which both $mu$ and $tau$ are epimorphisms (and
hence isomorphisms). We saw in @cor:progenerator-morita-equivalence that the
Morita context derived from a progenerator $M_Delta$ #source(175)of
$cal(M)_Delta$ always gives a Morita equivalence, and in that special case we
constructed an equivalence of categories
$cal(M)_Delta tilde.equiv cal(M)_Lambda$, where $Lambda = Hom_Delta (M, M)$. We
now prove that _every_ Morita equivalence of rings is derived from a
progenerator, and gives an equivalence of categories.

#theorem(major: true)[
  Let the rings $Delta$ and $Lambda$ be Morita equivalent relative to a Morita
  context $lmodule(Lambda, M)_Delta$, $lmodule(Delta, N)_Lambda$ as in
  @def:morita-context. Then
  + $M$ is a progenerator for both $cal(M)_Delta$ and $lmodule(Lambda, cal(M))$.

    $N$ is a progenerator for both $lmodule(Delta, cal(M))$ and $cal(M)_Lambda$.
  + There are bimodule isomorphisms
    $
      N tilde.equiv Hom_Delta (M, Delta) tilde.equiv Hom_Lambda (M, Lambda),
      quad
      M tilde.equiv Hom_Lambda (N, Lambda) tilde.equiv Hom_Delta (N, Delta).
    $
  + There are ring isomorphisms
    $
      Lambda tilde.equiv Hom_Delta (M, M) tilde.equiv Hom_Delta (N, N), quad
      Delta tilde.equiv Hom_Lambda (M, M) tilde.equiv Hom_Lambda (N, N),
    $
    where $Hom_Delta (N, N)$ acts as a ring of right operators on $N$, and
    likewise $Hom_Lambda (M, M)$ on $M$.
  + There are inverse pairs of equivalences of categories
    $
      #arrow-pair($cal(M)_Lambda$, $cal(M)_Delta","$, $S$, $T$) quad
      #arrow-pair(
        $lmodule(Lambda, cal(M))$,
        $lmodule(Delta, cal(M))","$,
        $S'$,
        $T'$,
      )
    $
    where
    $
      S & = dot times.o_Lambda M tilde Hom_Lambda (N, dot), quad
      && T = dot times.o_Delta N tilde Hom_Delta (M, dot), \
      S' & = N times.o_Lambda dot tilde Hom_Lambda (M, dot), quad
      && T' = M times.o_Delta dot tilde Hom_Delta (N, dot).
    $
  + The correspondence $J -> J M$ gives an isomorphism of the lattice of right
    ideals of $Lambda$ and the lattice of submodules of $M_Delta$, and the
    two-sided ideals correspond to sub-bimodules of $lmodule(Lambda, M)_Delta$.

    The correspondence $I -> M I$ gives an isomorphism of the lattice of left
    ideals of $Delta$ and the lattice of submodules of $lmodule(Lambda, M)$, and
    the two-sided ideals correspond to sub-bimodules of
    $lmodule(Lambda, M)_Delta$.

    The correspondence $I -> Hom_Delta (M, M I)$ gives an isomorphism between
    the lattice of two-sided ideals of $Delta$ and the lattice of two-sided
    ideals of $Lambda$, once we identify $Lambda$ with $Hom_Delta (M, M)$.
] <th:morita-equivalence>

#proof[
  By hypothesis both $mu$ and $tau$ in @def:morita-context are epic, so there
  exist $m$'s in $M$, $n$'s in $N$ such that
  $
    sum (m_i, n_i) = 1_Lambda, quad sum [n'_j, m'_j] = 1_Delta.
  $ <eq:morita-units>
  It is easily checked that for $n in N$,
  $
    (dot, n) in Hom_Lambda (M, Lambda), quad [n, dot] in Hom_Delta (M, Delta).
  $
  #source(176)The first equation in @eq:morita-units then asserts that
  $lmodule(Lambda, M)$ has trace ideal $Lambda$, whence $lmodule(Lambda, M)$ is
  a generator of $lmodule(Lambda, cal(M))$ by @cor:generator-trace-ideal.
  Likewise, the second equation in @eq:morita-units implies that $M_Delta$ is a
  generator of $cal(M)_Delta$. Further, since $mu$ is epic, it follows from
  @th:mu-epic that $M_Delta$ is finitely generated and projective; the same
  holds for $lmodule(Lambda, M)$ since $tau$ is epic. This proves the first part
  of (i), and the second part follows by symmetry.

  The assertions in (ii) and (iii) are immediate consequences of @th:mu-epic,
  using symmetry arguments. (See also Exercise~@exc:morita-context-symmetry). To
  prove (iv) we observe that for each $X in cal(M)_Lambda$,
  $
    {(dot times.o N)(dot times.o M)} X
    & = (X times.o_Lambda M) times.o_Delta N
    tilde.equiv X times.o_Lambda (M times.o_Delta N) \
    & tilde.equiv X times.o_Lambda Lambda tilde.equiv X,
  $
  since $M times.o_Delta N tilde.equiv Lambda$ as $Lambda$-$Lambda$-bimodules.
  All of these isomorphisms are natural in $X$, and thus
  $(dot times.o N)(dot times.o M)$ is naturally equivalent to the identity
  functor on $cal(M)_Lambda$. Analogous arguments hold for the other functors in
  (iv), so we obtain category equivalences, as claimed. The natural equivalences
  of the type $dot times.o_Lambda M tilde Hom_Lambda (N, dot)$ follow from (ii)
  and @eq:hom-tensor-dual-equivalence.

  Finally $S(Lambda) = M$, so the right ideal $J$ of $Lambda$ maps onto
  $S(J) = J times.o_Lambda M$. But $J times.o_Lambda M tilde.equiv J M$ as
  $Delta$-modules, since $lmodule(Lambda, M)$ is projective. This implies the
  first statement in (v). The second statement follows by symmetry. Finally, if
  $I$ is a two-sided ideal of $Delta$, then $I$ corresponds to the sub-bimodule
  $M I$ of $lmodule(Lambda, M)_Delta$, and this in turn corresponds (via $T$) to
  the two-sided ideal $Hom_Delta (M, M I)$. This completes the proof.
]

Let us briefly consider the special case where $M_Delta$ is free on $r$
generators, and where
$
  Lambda = Hom_Delta (M, M) tilde.equiv M_r (Delta).
$ <eq:free-module-endomorphisms>
Clearly $M_Delta$ is a progenerator for $cal(M)_Delta$, and there is a category
equivalence
$
  Hom_Delta (M, dot) : cal(M)_Delta -> cal(M)_Lambda.
$
The isomorphism in @eq:free-module-endomorphisms can be described explicitly,
once we start with a free $Delta$-basis ${m_1, dots, m_r}$ of $M$. Each
$f in Lambda$ determines a matrix $T_f in M_r (Delta)$, such that
$
  f(m_1, dots, m_r) = (m_1, dots, m_r) T_f.
$
This equation means that
$
  f(m_j) = sum_(i=1)^r m_i tau_(i j), quad 1 <= j <= r, quad
  T_f = (tau_(i j)).
$ <eq:endomorphism-matrix>

For any two-sided ideal $I$ of the ring $Delta$, let $M_r (I)$ denote the set of
all $r times r$ matrices with entries in $I$.

#corollary[
  #source(177)The map $I -> M_r (I)$ gives an isomorphism between the lattice of
  two-sided ideals of $Delta$ and the lattice of two-sided ideals of
  $M_r (Delta)$.
] <cor:matrix-ring-ideals>

#proof[
  By @th:morita-equivalence[(v)], the map $I -> Hom_Delta (M, M I)$ gives the
  desired isomorphism, once we identify $Lambda$ with $M_r (Delta)$ as in
  @eq:free-module-endomorphisms. We have
  $
    M = dsum_(k=1)^r m_k Delta, quad M I = dsum_(k=1)^r m_k I,
  $
  where ${m_1, dots, m_r}$ is a free $Delta$-basis for $M$. Let $f in Lambda$
  correspond to $T_f in M_r (Delta)$, as in @eq:endomorphism-matrix. It is clear
  that $f in Hom_Delta (M, M I)$ if and only if each $tau_(i j)$ in
  @eq:endomorphism-matrix lies in $I$. Hence the image of $Hom_Delta (M, M I)$
  in $M_r (Delta)$ is precisely $M_r (I)$, which proves the corollary.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Keep the notation in @eq:derived-context-rings–@eq:derived-context-trace.
  Prove that if $mu$ is epic, then $mu$ is monic, and likewise for $tau$.
  #hint[@exc:morita-epic-implies-monic][It suffices to prove the result for
    $mu$, by symmetry. Let $mu$ be epic, and write
    $1_Lambda = sum_1^r (m_i, f_i)$. Let $sum n_j times.o g_j in ker mu$, so
    $sum (n_j, g_j) = 0$. Then
    $
      sum_j n_j times.o g_j & = sum_(i, j) (m_i, f_i) n_j times.o g_j
                              = sum m_i times.o [f_i, n_j] g_j \
                            & = sum m_i times.o f_i (n_j, g_j) = 0.
    $] <hint:morita-epic-implies-monic>
] <exc:morita-epic-implies-monic>

#exercise[
  Consider an equivalence of categories
  $cal(M)_Lambda lrmaps(S, T) cal(M)_Delta$, where $Lambda, Delta$ are rings.
  Show that this equivalence comes from a Morita context.
  #hint[@exc:equivalence-from-morita-context][Set $M = T(Delta)$,
    $N = S(Lambda)$. Then there are bimodule structures
    $lmodule(Delta, M)_Lambda$, $lmodule(Lambda, N)_Delta$ which give a Morita
    equivalence between $Lambda$ and $Delta$. Further, the functors $S$ and
    $dot times.o N$ are naturally equivalent, as are $T$ and
    $dot times.o M$.] <hint:equivalence-from-morita-context>
] <exc:equivalence-from-morita-context>

#exercise[
  Let $M$ be a free right $Delta$-module on $r$ generators, and set
  $Lambda = Hom_Delta (M, M)$. Then $M$ is a progenerator for $cal(M)_Delta$,
  and there is an equivalence of categories
  $
    #arrow-pair(
      $cal(M)_Delta$,
      $cal(M)_Lambda$,
      $dot times.o M^*$,
      $dot times.o M$,
    )
  $
  where $M^* = Hom_Delta (M, Delta)$. What is the two-sided ideal in $Lambda$
  which corresponds to a given two-sided ideal $J$ in $Delta$?
] <exc:free-module-ideal-correspondence>

#exercise[
  Show that Morita equivalent rings have isomorphic centers.
  #hint[@exc:morita-centers][Identify the center of $Lambda$ with the ring of
    bimodule endomorphisms of $lmodule(Lambda, M)_Delta$.]
  <hint:morita-centers>
] <exc:morita-centers>

#exercise[
  Let $R$ be a commutative ring, $Lambda$ a left noetherian $R$-algebra, and $M$
  a finitely generated left $Lambda$-module. Suppose that for each maximal ideal
  $P$ of $R$, the localization $M_P$ is a generator for the category of left
  $Lambda_P$-modules. Prove that $M$ is a generator for
  $lmodule(Lambda, cal(M))$. Also prove the corresponding statement when
  "generator" is replaced by "progenerator".
] <exc:generator-local>

#exercise[
  Let $hat(R)$ be the completion of the commutative local noetherian ring $R$,
  let $Lambda$ be a #source(178)left noetherian $R$-algebra, and let $M$ be a
  finitely generated left $Lambda$-module. Show that $M$ is a generator of
  $lmodule(Lambda, cal(M))$ if and only if $hat(R) times.o_R M$ is a generator
  of $lmodule(hat(Lambda), cal(M))$, where
  $hat(Lambda) = hat(R) times.o_R Lambda$. Prove the corresponding result for
  progenerators.
] <exc:generator-completion>

#exercise[
  Show that the isomorphisms in @th:morita-equivalence[(ii)] are given as
  follows:
  $
    N & tilde.equiv Hom_Delta (M, Delta), n -> [n, dot]; quad
    && N tilde.equiv Hom_Lambda (M, Lambda), n -> (dot, n). \
    M & tilde.equiv Hom_Lambda (N, Lambda), m -> (m, dot); quad
    && M tilde.equiv Hom_Delta (N, Delta), m -> [dot, m].
  $
  Further, each isomorphism in @th:morita-equivalence[(iii)] is given by letting
  the elements of $Lambda$ and $Delta$ act as left or right multiplications on
  the modules $M$ or $N$.
] <exc:morita-context-symmetry>

#exercise[
  Show that Morita equivalence of rings is transitive.
] <exc:morita-transitive>

#exercise[
  Let $M$ be a minimal left ideal of the simple left artinian ring $Lambda$.
  Prove that $M$ is a progenerator for $lmodule(Lambda, cal(M))$. Set
  $Delta = Hom_Lambda (M, M)$, and view $M$ as a bimodule
  $lmodule(Lambda, M)_Delta$. Prove
  + $Delta$ is a skewfield.
  + $M$ is a finite dimensional $Delta$-space.
  + $Lambda tilde.equiv Hom_Delta (M, M)$.
  #hint[@exc:morita-wedderburn-a][Use @cor:generator-trace-ideal to show that
    $M$ is a generator for $lmodule(Lambda, cal(M))$. By Schur's Lemma, $Delta$
    is a skewfield. Assertions (ii) and (iii) then follow from
    @th:morita-equivalence. This provides another proof of the harder part of
    Wedderburn's Theorem @th:wedderburn.] <hint:morita-wedderburn-a>
] <exc:morita-wedderburn-a>

#exercise[
  Let $Delta$ be a skewfield, $V_Delta = Delta^((r))$ a right $Delta$-space, and
  let $Lambda = Hom_Delta (V, V)$. Prove that $Lambda$ is a simple left artinian
  ring, and that $Delta = Hom_Lambda (V, V)$.
  #hint[@exc:morita-wedderburn-b][View $V$ as a bimodule
    $lmodule(Lambda, V)_Delta$. By @cor:matrix-ring-ideals, the ring $Lambda$ is
    simple. Its left ideals satisfy the D.C.C., since they are in bijection with
    the set of $Delta$-subspaces of $V$ by @th:morita-equivalence. Finally,
    $Delta tilde.equiv Hom_Lambda (V, V)$ by @th:morita-equivalence. This proves
    the easier part of Wedderburn's Theorem @th:wedderburn.]
  <hint:morita-wedderburn-b>
] <exc:morita-wedderburn-b>
