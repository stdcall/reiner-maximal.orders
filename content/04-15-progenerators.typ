#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/common.typ": ladder
#import "diagrams/04-15-progenerators.typ": arrow-pair, left-labelled-square

== Progenerators <sec:progenerators>

We shall use the notation of §~@ss:functors-and-categories. Let $cal(A)$ be a
category with objects $A, A', dots$, and $cal(B)$ a category with objects
$B, B', dots$. We shall write $A in cal(A)$ to indicate that $A$ is an object in
$cal(A)$. All functors $F : cal(A) -> cal(B)$ considered below are assumed to be
additive. Unless otherwise stated, functors are taken to be covariant.

Let $F : cal(A) -> cal(B)$ and $G : cal(A) -> cal(B)$ be a pair of functors. A
_natural transformation_ $t : F -> G$ is a family
#idx("natural transformation")
$
  t = {t_A : A in cal(A)},
$
where for each $A in cal(A)$,
$
  t_A in Hom_(cal(B)) (F A, G A),
$
and where for each $alpha in Hom(A, A')$, the diagram
$
  #left-labelled-square(
    $F A$,
    $G A$,
    $F A'$,
    $G A'$,
    $t_A$,
    $t_(A')$,
    $F alpha$,
    $G alpha$,
    bottom-below: true,
  )
$
is commutative. If furthermore each $t_A$ is an isomorphism, we call the
functors $F$ and $G$ _naturally equivalent_, and write $F tilde G$.
#idx("natural equivalence")

#example(numbered: false)[
  Let $cal(A) = cal(B) = lmodule(Lambda, cal(M))$, $F$ the identity functor, $G$
  the functor $Lambda times.o_Lambda dot$. For each $A in cal(A)$, let
  $t_A : A -> Lambda times.o_Lambda A$ be the left $Lambda$-isomorphism given in
  @th:tensor-isomorphisms. Then $t$ is a natural equivalence from $F$ to $G$.
]

#source(164)Let $i d_(cal(A))$ be the identity functor on $cal(A)$. Two
categories $cal(A)$ and $cal(B)$ are called _equivalent_ if there exist functors
$F, G$: #idx("equivalence", "of categories")#idx("isomorphism of categories")
$
  #arrow-pair($cal(A)$, $cal(B)$, $F$, $G$)
$
such that $G F tilde i d_(cal(A))$ and $F G tilde i d_(cal(B))$. For example, if
$Lambda^circle.stroked.tiny$ denotes the opposite ring of $Lambda$ (same
elements, but multiplication is reversed), then the categories
$lmodule(Lambda, cal(M))$ and $cal(M)_(Lambda^circle.stroked.tiny)$ are
equivalent.

Now let $F : cal(A) -> cal(B)$ be any functor. Call $F$ _faithful_ if the map
#idx("faithful functor")
$
  alpha in Hom(A, A') -> F alpha in Hom(F A, F A')
$ <eq:functor-on-maps>
is injective, that is, if $F alpha = 0$ implies that $alpha = 0$. For example,
if $M$ is a faithfully flat right $Lambda$-module, then the functor
$M times.o_Lambda dot : lmodule(Lambda, cal(M)) -> Ab$ is faithful (see
@th:faithfully-flat-criteria).

On the other hand, the functor $F : cal(A) -> cal(B)$ is _full_ if the map in
@eq:functor-on-maps is surjective, that is, if each $beta in Hom(F A, F A')$
equals some $F alpha$. For example, let $overline(Lambda) = Lambda slash I$
where $I$ is a two-sided ideal of $Lambda$. Let $cal(A)$ be the category of
projective left $Lambda$-modules, $cal(B)$ the corresponding category for
$overline(Lambda)$, and let $F : cal(A) -> cal(B)$ be given by
$F(M) = M slash I M$. Then $F$ is a full functor, since each
$overline(Lambda)$-homomorphism $beta : M slash I M -> N slash I N$, where
$M, N in cal(A)$, can be lifted to a $Lambda$-homomorphism $alpha : M -> N$, and
thus $beta = F alpha$.
#idx("full functor")

We recall from @th:projective-criteria that an object $X in cal(A)$ is
_projective_ if the functor #idx("projective object")
$
  Hom(X, dot) : cal(A) -> Ab
$
is exact. This functor carries $A in cal(A)$ onto the abelian group $Hom(X, A)$,
and takes each $alpha in Hom(A, A')$ onto
$
  alpha_* : Hom(X, A) -> Hom(X, A'),
$
where $alpha_* f = alpha f$, $f in Hom(X, A)$.

Whether or not $X$ is projective, let us consider the functor $Hom(X, dot)$. We
call $X$ a _generator_ of the category $cal(A)$ if $Hom(X, dot)$ is a faithful
functor, that is, if $alpha_* = 0$ implies that $alpha = 0$. In other words, $X$
is a generator if and only if for each nonzero $alpha : A -> A'$ there exists an
$f : X -> A$ such that $alpha f != 0$.
#idx("generator (of category)")

Dually, $X in cal(A)$ is _injective_ if the contravariant functor $Hom(dot, X)$
is exact, while $X$ is a _cogenerator_ for $cal(A)$ if $Hom(dot, X)$ is
faithful.

#theorem[
  An object $X$ in the category $cal(A)$ is a generator for $cal(A)$ if and only
  if every $A in cal(A)$ is a quotient of a direct sum of copies of $X$.
] <th:generator-quotients>

#proof[
  Let $X$ be a generator, and let $A in cal(A)$. For each $f in Hom(X, A)$, let
  $X_f$ be a copy of $X$, and set $Y = dsum_f X_f$. Each $X_f$ maps into $A$ (by
  means of $f$), #source(165)so there is a map $eta : Y -> A$, defined by
  $eta = dsum f$. Thus
  $
    eta(sum x_f) = sum f(x_f), quad x_f in X_f.
  $
  Clearly
  $
    im eta = sum_(f in Hom(X, A)) f(X) subset A.
  $ <eq:image-of-generator-sum>
  Let us show that $im eta = A$; if not, there exists a nonzero map
  $
    alpha : A -> A slash im eta.
  $
  Since $X$ is a generator, there must be an $f : X -> A$ such that
  $alpha f != 0$. But $(alpha f) X = alpha(f(X)) = 0$, since
  $f(X) subset im eta$. This gives a contradiction, and shows that $eta$ is an
  epimorphism of $Y$ onto $A$. Therefore $A$ is a quotient of a direct sum of
  copies of $X$, as claimed.

  Conversely, suppose that for each $A in cal(A)$ there is an epimorphism
  $xi : dsum X_i -> A$, where each $X_i$ is a copy of $X$. We must show that $X$
  is a generator for $cal(A)$. Let $alpha : A -> A'$ be nonzero; then also
  $alpha xi != 0$, since $xi$ is epic. If we write $xi = dsum xi_i$, where
  $xi_i : X_i -> A$, then $alpha xi = dsum alpha xi_i$. Therefore
  $alpha xi_i != 0$ for some $i$. But $X_i tilde.equiv X$, and so there exists
  an $f : X -> A$ such that $alpha f != 0$. This proves that $X$ is a generator
  for $cal(A)$, as desired.
]

The construction in @eq:image-of-generator-sum is of special importance in the
following circumstance. Let $X in lmodule(Lambda, cal(M))$, and define the
_trace ideal_ of $X$ as #idx("trace ideal")
$
  "trace" X = sum_(f in Hom_Lambda (X, Lambda)) f(X) subset Lambda.
$ <eq:trace-ideal>
It is easily verified that $"trace" X$ is a two-sided ideal of $Lambda$.

#corollary[
  The left $Lambda$-module $X$ is a generator for $lmodule(Lambda, cal(M))$ if
  and only if $"trace" X = Lambda$.
] <cor:generator-trace-ideal>

#proof[
  If $"trace" X = Lambda$, then the proof of the preceding theorem shows that
  $Lambda$ is a quotient module of $dsum X_i$, where each $X_i tilde.equiv X$.
  But every $Lambda$-module $A$ is a quotient of a direct sum $dsum Lambda_j$,
  with each $Lambda_j tilde.equiv Lambda$. Hence $A$ is also a quotient of a
  direct sum of copies of $X$, whence $X$ is a generator for
  $lmodule(Lambda, cal(M))$ by @th:generator-quotients.

  Suppose conversely that $X$ is a generator. The proof of
  @th:generator-quotients shows that $im eta = A$ in @eq:image-of-generator-sum,
  where $A$ is any $Lambda$-module. Taking $A = lmodule(Lambda, Lambda)$, we see
  that the trace ideal of $X$ equals $im eta$, and thus coincides with $Lambda$
  as claimed.
]

It is clear from @th:generator-quotients, or directly from the definition of
generator, that $Lambda$ is itself a generator for the category
$lmodule(Lambda, cal(M))$. Indeed, every nonzero free module is a generator.

Given a possibly infinite family ${X_lambda}$ of objects in $cal(A)$, we may
form their #source(166)direct sum $dsum X_lambda$. There are the usual injection
maps ${i_lambda}$ and projection maps ${p_lambda}$, with
$
  #arrow-pair($X_lambda$, $dsum_nu X_nu.$, $i_lambda$, $p_lambda$)
$
We shall say that a functor $F : cal(A) -> cal(B)$ _preserves direct sums_ if
for each family ${X_lambda}$, there is an isomorphism #idx(
  "preserves direct sums",
)
$
  F(dsum_nu X_nu) tilde.equiv dsum_nu F X_nu,
$
induced by the maps ${F i_lambda, F p_lambda}$. For example, tensor product
functors preserve direct sums. So also does the functor $Hom_Lambda (P, dot)$,
where $P$ is any finitely generated projective $Lambda$-module (see
Exercise~@exc:hom-preserves-direct-sums).

#theorem[
  Let $F : cal(A) -> cal(B)$ and $G : cal(A) -> cal(B)$ be a pair of right exact
  functors which preserve direct sums. Let $t : F -> G$ be a natural
  transformation, and let $X$ be a generator for $cal(A)$. If
  $t_X : F X tilde.equiv G X$ is an isomorphism in the category $cal(B)$, then
  $t$ is a natural equivalence of functors.
] <th:natural-equivalence-on-generator>

#proof[
  Since $t = {t_A : A in cal(A)}$ is a natural transformation, each
  $alpha : A -> A'$ gives rise to a commutative diagram
  $
    #left-labelled-square(
      $F A$,
      $F A'$,
      $G A$,
      $G A'.$,
      $F alpha$,
      $G alpha$,
      $t_A$,
      $t_(A')$,
    )
  $
  We are assuming that $t_X$ is an isomorphism, and are trying to prove that
  each $t_A$ is an isomorphism.

  Since $X$ is a generator of $cal(A)$, each $A in cal(A)$ is a quotient of a
  direct sum $dsum X$ of copies of $X$. Hence there is an $cal(A)$-exact
  sequence
  $
    U -> V -> A -> 0, quad "where" quad U = dsum X, quad V = dsum X.
  $
  But $F$ is right exact, and so the sequence
  $
    F U -> F V -> F A -> 0
  $
  is $cal(B)$-exact. Hence there is a commutative diagram with exact rows:
  $
    #ladder(
      ($F U$, $F V$, $F A$, $0$),
      ($G U$, $G V$, $G A$, $0.$),
      ($t_U$, $t_V$, $t_A$, none),
    )
  $
  Now $F U tilde.equiv dsum F X$, $G U tilde.equiv dsum G X$, because $F$ and
  $G$ preserve direct sums by hypothesis. Since $t_X : F X tilde.equiv G X$, it
  follows that $t_U : F U tilde.equiv G U$. Likewise $t_V$ is an isomorphism,
  and the commutativity of the above diagram shows that $t_A$ is also an
  isomorphism, as desired.
]

#source(167)An object $P in cal(A)$ is _faithfully projective_ if it satisfies
the following three conditions: #idx("faithfully projective")
+ $P$ is a projective object in $cal(A)$.
+ $P$ is a generator for $cal(A)$.
+ $Hom(P, dot)$ preserves direct sums.
In particular, considering the category $lmodule(Lambda, cal(M))$, we call a
left $Lambda$-module $P$ a _progenerator_ for $lmodule(Lambda, cal(M))$ if
#idx("progenerator")
+ $P$ is a finitely generated projective $Lambda$-module, and
+ $P$ is a generator for $lmodule(Lambda, cal(M))$.
Note each such $P$ is faithfully projective, since by
Exercise~@exc:hom-preserves-direct-sums $Hom(P, dot)$ necessarily preserves
direct sums.

#theorem[
  Let $P$ be a faithfully projective object in the category $cal(A)$, and let
  $
    Lambda = Hom_(cal(A)) (P, P), quad cal(B) = lmodule(Lambda, cal(M)).
  $
  View $P$ as right $Lambda$-module. Then the functor
  $
    Hom(P, dot) : cal(A) -> cal(B)
  $
  gives an equivalence of categories.
] <th:faithfully-projective-equivalence>

#proof[
  It is clear that $Lambda$ is a ring, and that $P$ can be viewed as a right
  $Lambda$-module. Then for each $A in cal(A)$, $Hom_(cal(A)) (P, A)$ is a left
  $Lambda$-module. Thus the functor $F : cal(A) -> cal(B)$, given by
  $F(A) = Hom(P, A)$, is well defined. Clearly $F P = Lambda$. Since $P$ is a
  projective object, the functor $F$ is exact.

  In order to show that $F$ is a category equivalence, we use the result of
  Exercise~@exc:equivalence-criterion. We show first that $F$ is full and
  faithful, that is, for each pair $A, A' in cal(A)$, the map
  $
    F : Hom(A, A') -> Hom(F A, F A')
  $ <eq:full-faithful-map>
  given by $alpha -> F alpha$, is an isomorphism. Let us first verify this when
  $A = dsum P_lambda$, where each $P_lambda tilde.equiv P$. By
  @th:hom-isomorphisms
  $
    Hom(A, A') tilde.equiv product Hom(P_lambda, A')
    tilde.equiv product_lambda F A',
  $
  the latter because $Hom(P_lambda, A') tilde.equiv Hom(P, A') = F A'$. On the
  other hand, $F$ preserves direct sums since $P$ is faithfully projective, and
  thus
  $
    Hom_Lambda (F A, F A') tilde.equiv Hom_Lambda (dsum F P_lambda, F A')
    tilde.equiv product_lambda Hom_Lambda (Lambda, F A')
    tilde.equiv product_lambda F A'.
  $
  We have now shown that the map $F$ in @eq:full-faithful-map is an isomorphism
  whenever $A$ is a direct sum of copies of $P$.

  #source(168)Now let $A$ and $A'$ be arbitrary, and let
  $
    U -> V -> A -> 0
  $
  be an $cal(A)$-exact sequence in which $U$ and $V$ are direct sums of copies
  of $P$. Then the sequence
  $
    F U -> F V -> F A -> 0
  $
  is $cal(B)$-exact, since $F$ is an exact functor. Since $Hom$ is a left exact
  functor, we obtain a commutative diagram with exact rows
  $
    #ladder(
      ($0$, $Hom(A, A')$, $Hom(V, A')$, $Hom(U, A')$),
      ($0$, $Hom(F A, F A')$, $Hom(F V, F A')$, $Hom(F U, F A').$),
      (none, $F_1$, $F_2$, $F_3$),
      down-side: right,
      gap: 4mm,
    )
  $
  By the preceding paragraph, both $F_2$ and $F_3$ are isomorphisms. Hence so is
  $F_1$, and this completes the proof that $F : cal(A) -> cal(B)$ is a full and
  faithful functor. (For another proof see
  Exercise~@exc:full-faithful-direct-proof.)

  In order to deduce that $F$ gives an equivalence of categories, it remains for
  us to show that every left $Lambda$-module $M$ is of the form $F A$ for some
  $A in cal(A)$. Let us first write a $Lambda$-exact sequence
  $
    X_1 stretch(->)_xi X_0 -> M -> 0, quad X_0, X_1 quad Lambda"-free".
  $
  Since $Lambda = F(P)$, we may write $X_i = F(U_i)$, with $U_i$ a direct sum of
  copies of $P$, $i = 0, 1$. By the preceding paragraphs,
  $
    Hom(X_1, X_0) = Hom(F(U_1), F(U_0)) tilde.equiv Hom(U_1, U_0),
  $
  so we have $xi = F alpha$ for some $alpha : U_1 -> U_0$. Let $A = cok alpha$,
  and apply $F$ to the $cal(A)$-exact sequence
  $
    U_1 stretch(->)_alpha U_0 -> A -> 0,
  $
  thus obtaining a $Lambda$-exact sequence
  $
    X_1 stretch(->)_xi X_0 -> F A -> 0.
  $
  Therefore $M tilde.equiv F A$, and the proof of the theorem is complete.
]

#corollary(major: true)[
  Let $M$ be a progenerator for the category $lmodule(Delta, cal(M))$, where
  $Delta$ is a ring, and let $Lambda = Hom_Delta (M, M)$ be the endomorphism
  ring of $M$. View $M$ as a bimodule $lmodule(Delta, M)_Lambda$. Then there is
  an equivalence of categories
  $
    Hom_Delta (M, dot) : lmodule(Delta, cal(M)) -> lmodule(Lambda, cal(M)).
  $
] <cor:progenerator-equivalence>

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  #source(169)Let $F : cal(A) -> cal(B)$ be an equivalence of categories. Show
  that $A$ is projective if and only if $F A$ is projective.
] <exc:equivalence-preserves-projectives>

#exercise[
  Let $F : cal(A) -> cal(B)$ be a full faithful functor such that every
  $B in cal(B)$ is the image $F A$ of some $A in cal(A)$. Prove that $F$ is a
  category equivalence.
] <exc:equivalence-criterion>

#exercise[
  Let $P$ be a finitely generated projective left $Lambda$-module. Show that the
  functor
  $
    Hom_Lambda (P, dot) : lmodule(Lambda, cal(M)) -> Ab
  $
  preserves direct sums. #hint[@exc:hom-preserves-direct-sums][First check the
    case where $P = Lambda$, then use the fact that
    $
      Hom_Lambda (P dotplus P', dot) tilde
      Hom_Lambda (P, dot) dotplus Hom_Lambda (P', dot).
    $] <hint:hom-preserves-direct-sums>
] <exc:hom-preserves-direct-sums>

#exercise[
  Let $lmodule(Lambda, cal(M)) -> lmodule(Delta, cal(M))$ be an equivalence of
  categories, where $Lambda$ and $Delta$ are rings. Show that $Lambda$ is left
  hereditary if and only if $Delta$ is left hereditary.
  #hint[@exc:equivalence-preserves-hereditary][$Lambda$ is left hereditary if
    and only if subobjects of projective objects in $lmodule(Lambda, cal(M))$
    are projective.] <hint:equivalence-preserves-hereditary>
] <exc:equivalence-preserves-hereditary>

#exercise[
  Let $Ab^circle.stroked.tiny$ denote the category which is opposite to $Ab$,
  that is, $Ab^circle.stroked.tiny$ has the same objects as $Ab$, but all arrows
  are reversed.
  + Prove that direct products in $Ab$ correspond to direct sums in
    $Ab^circle.stroked.tiny$.
  + Given an object $A'$ in a category $cal(A)$, define a functor
    $G : cal(A) -> Ab^circle.stroked.tiny$ by setting
    $
      G(A) = {Hom_(cal(A)) (A, A')}^circle.stroked.tiny
      in Ab^circle.stroked.tiny, quad "for each" A in cal(A).
    $
    (There is an obvious definition of the action of the functor $G$ on maps in
    $cal(A)$.) Prove that $G$ is a right exact covariant functor which preserves
    direct sums!
] <exc:opposite-hom-functor>

#exercise[
  Use @th:natural-equivalence-on-generator[Theorem] to prove that the map $F$ in
  @eq:full-faithful-map is an isomorphism.
  #hint[@exc:full-faithful-direct-proof][Keep the notation of the proof of
    @th:faithfully-projective-equivalence, so
    $
      F(A') = Hom_(cal(A)) (P, A') quad "for each" A' in cal(A).
    $
    Keeping $A'$ fixed, define functors
    $G, H : cal(A) -> Ab^circle.stroked.tiny$ by
    $
      G(A) = {Hom_(cal(A)) (A, A')}^circle.stroked.tiny, quad
      H(A) = {Hom_(cal(B)) (F A, F A')}^circle.stroked.tiny, quad A in cal(A),
    $
    with obvious definitions of $G$ and $H$ on maps. Since $P$ is a faithfully
    projective object in $cal(A)$, the functor $F$ is exact and preserves direct
    sums. Use this to prove that $H$ is a right exact covariant functor which
    preserves direct sums.

    The functor $F : cal(A) -> cal(B)$ determines homomorphisms
    $
      F_(A, A') : Hom_(cal(A)) (A, A') -> Hom_(cal(B)) (F A, F A'), quad
      A, A' in cal(A).
    $
    For each $A in cal(A)$, define $t_A : H A -> G A$ by
    $t_A = {F_(A, A')}^circle.stroked.tiny$. Prove that $t : H -> G$ is a
    natural transformation.

    In order to prove that the map $F$ in @eq:full-faithful-map is an
    isomorphism, it suffices to establish that each $t_A$ is an isomorphism in
    $Ab^circle.stroked.tiny$. By @th:natural-equivalence-on-generator, this will
    follow once we know that $t_P$ is an isomorphism in
    $Ab^circle.stroked.tiny$. But this is true since
    $
      G P & = Hom_(cal(A)) (P, A') = F A' \
      H P & = Hom_(cal(B)) (F P, F A') = Hom_Lambda (Lambda, F A')
            tilde.equiv F A'.
    $] <hint:full-faithful-direct-proof>
] <exc:full-faithful-direct-proof>

#exercise[
  #source(170)Let $P_Delta$ be a progenerator for $cal(M)_Delta$, and let
  $G, H : cal(M)_Delta -> Ab$ be the covariant functors defined by
  $
    G(L) = Hom_Delta (P, L), quad H(L) = L times.o_Delta P^*, quad
    L in cal(M)_Delta,
  $
  where $P^* = Hom_Delta (P, Delta)$ (viewed as left $Delta$-module). Show that
  the functors $G, H$ are naturally equivalent.
  #hint[@exc:hom-as-tensor-with-dual][Prove
    + $P^*$ is a finitely generated projective left $Delta$-module.
    + The functors $G$ and $H$ are exact, and preserve direct sums.
    + There is a natural transformation $t : H -> G$, given by
      $
        t_L : H(L) -> G(L), quad L in cal(M)_Delta,
      $
      where $t_L$ is defined by the formula
      $
        {t_L (l times.o phi)} x = l dot phi(x), quad l in L, quad
        phi in P^*, quad x in P.
      $
    + $t_Delta : H(Delta) tilde.equiv G(Delta)$.
    Then use @th:natural-equivalence-on-generator.]
  <hint:hom-as-tensor-with-dual>
] <exc:hom-as-tensor-with-dual>
