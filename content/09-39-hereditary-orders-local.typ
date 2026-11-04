#import "main-defs.typ": *
#import "statements.typ": *

== Local theory of hereditary orders <sec:hereditary-orders-local>

Throughout this section let $R$ be a complete discrete valuation ring with
maximal ideal $P = pi R$ and residue class field $overline(R)$. As we shall see,
the key to studying hereditary orders is the investigation of their Jacobson
radicals. The first result is due to Auslander–Goldman [@bib:Auslander1960a]:

#theorem[
  An $R$-order $Lambda$ is hereditary if and only if $rad Lambda$ is a
  projective left $Lambda$-module, or equivalently, if and only if $rad Lambda$
  is an invertible $(Lambda, Lambda)$-bimodule.
] <th:hereditary-radical-projective>

#proof[
  _Step 1._ Let $J = rad Lambda$. Surely $J$ is left $Lambda$-projective if
  $Lambda$ is hereditary. Conversely, assume that $lmodule(Lambda, J)$ is
  projective. We shall show that $Lambda$ is hereditary by proving that every
  left ideal $L$ of $Lambda$ is projective. Given any $L$, there is a
  $Lambda$-exact sequence
  $
    0 -> L' -> Lambda^((r)) -> L -> 0
  $
  #source(361)for some $r$, where $L'$ is a left $Lambda$-lattice. We prove
  below that $Ext^1 (L, L') = 0$, where $Ext$ means $Ext_Lambda$. Once this is
  known, it follows that the above sequence is $Lambda$-split. Therefore
  $L | Lambda^((r))$, so $L$ is $Lambda$-projective, whence $Lambda$ is
  hereditary as claimed.

  The $Lambda$-exact sequence
  $
    0 -> L stretch(->)^pi L -> L slash pi L -> 0
  $
  gives rise to an exact sequence
  $
    Ext^1 (L, L') stretch(->)^pi Ext^1 (L, L') -> Ext^2 (L slash pi L, L')
  $
  by @th:long-exact-ext, where the arrows labelled "$pi$" are the maps given by
  multiplication by $pi$. We set $M = L slash pi L$, and we show below that
  $Ext^2 (M, L') = 0$. This will imply that
  $
    pi dot Ext^1 (L, L') = Ext^1 (L, L'),
  $
  whence $Ext^1 (L, L') = 0$ by @th:finite-generation-hom-ext and
  @th:nakayama[Nakayama's Lemma].

  The left $Lambda$-module $M$ is artinian, since $pi M = 0$. We prove by
  induction on the $Lambda$-composition length of $M$ that $Ext^2 (M, L') = 0$
  for every left $Lambda$-module $L'$. Suppose first that $M$ is a simple
  $Lambda$-module; then $M$ is also a simple left $overline(Lambda)$-module,
  where $overline(Lambda)$ is the semisimple artinian ring $Lambda slash J$.
  Therefore $M | overline(Lambda)$, whence $Ext^2 (M, L')$ is a direct summand
  of $Ext^2 (overline(Lambda), L')$ by @rem:ext-properties[(iv)]. However, there
  is a $Lambda$-exact sequence
  $
    0 -> J -> Lambda -> overline(Lambda) -> 0,
  $
  and $lmodule(Lambda, J)$ is projective by hypothesis. Hence by @eq:ext-n we
  obtain $Ext_Lambda^2 (overline(Lambda), L') = 0$ for all $L'$. Therefore
  $Ext^2 (M, L') = 0$ for all simple $Lambda$-modules $M$ and all
  $Lambda$-modules $L'$.

  Now suppose that the $Lambda$-module $M$ has composition length at least two,
  and let $S$ be any simple submodule of $M$. The $Lambda$-exact sequence
  $
    0 -> S -> M -> M slash S -> 0
  $
  gives an exact sequence
  $
    Ext^2 (M slash S, L') -> Ext^2 (M, L') -> Ext^2 (S, L').
  $
  Since the first term vanishes by the induction hypothesis, and since the last
  term is 0, it follows that $Ext^2 (M, L') = 0$ for all $L'$. This completes
  the proof that $Lambda$ is left hereditary whenever $lmodule(Lambda, J)$ is
  projective. Analogously, $Lambda$ is right hereditary whenever $J_Lambda$ is
  projective.

  _Step 2._ We now prove that $Lambda$ is hereditary if and only if $J$ is an
  invertible $(Lambda, Lambda)$-bimodule. If $J$ is invertible, then
  $lmodule(Lambda, J)$ is projective by @th:derived-context-epic or
  §~@sec:picard-groups, whence $Lambda$ is hereditary. For the harder part of
  the proof, suppose now that #source(362)$Lambda$ is hereditary, so both
  $lmodule(Lambda, J)$ and $J_Lambda$ are projective modules. Then
  $J | Lambda^((r))$ for some $r$. We shall use this fact in a moment.

  Let
  $
    Lambda = dsum_(i=1)^t M_i, quad {M_i} "indecomposable left ideals,"
  $
  with the ${M_i}$ numbered so that ${M_1, dots, M_u}$ are a full set of
  non-isomorphic modules among the ${M_i}$. Setting
  $overline(M)_i = M_i slash J M_i$, it follows from
  @cor:complete-local-decomposition that ${overline(M)_1, dots, overline(M)_u}$
  are a full set of non-isomorphic simple left $(Lambda slash J)$-modules.

  Since $J | Lambda^((r))$, it follows by Exercise~@exc:summand-of-sum that
  $
    J tilde.equiv dsum_(i=1)^u M_i^((n_i))
  $
  for some non-negative integers ${n_i}$. Therefore
  $
    J slash J^2 tilde.equiv dsum_(i=1)^u overline(M)_i^((n_i))
    quad "as left" Lambda"-modules,"
  $
  and so each $n_i > 0$ by Exercise~@exc:simple-in-radical-layer. Thus
  $Lambda | J^((s))$ for some $s$, whence by @th:generator-quotients
  $lmodule(Lambda, J)$ is a progenerator for the category
  $lmodule(Lambda, cal(M))$. Setting $Delta = Hom_Lambda (J, J)$, it follows
  from @cor:progenerator-morita-equivalence that the rings $Lambda$, $Delta$ are
  Morita equivalent, so $lmodule(Lambda, J)_Delta$ is an invertible bimodule
  (see §~@sec:picard-groups) and $Lambda = Hom_Delta (J, J)$. Using the
  identification $Hom_Delta (J, J) = O_l (J)$, we conclude at once that
  $Lambda = O_l (J)$. But then, by symmetry, also $Lambda = O_r (J)$. Therefore
  $J$ is an invertible $(Lambda, Lambda)$-bimodule, as claimed. This completes
  the proof of the theorem. (See also Remark following
  @cor:hereditary-chain-properties.)
]

As preparation for our later discussion, we introduce the following notation:

#definition[
  Let $Gamma$ be a ring. For each ideal $frak(a)$ of $Gamma$, let
  $(frak(a))^(m times n)$ denote the set of all $m times n$ matrices with
  entries in $frak(a)$. If ${frak(a)_(i j) : 1 <= i, j <= r}$ is a set of ideals
  in $Gamma$, we write
  $
    Lambda = mat(
      delim: "[",
      (frak(a)_11), (frak(a)_12), dots, (frak(a)_(1 r));
      (frak(a)_21), (frak(a)_22), dots, (frak(a)_(2 r));
      dots.h, dots.h, dots.h, dots.h;
      (frak(a)_(r 1)), (frak(a)_(r 2)), dots, (frak(a)_(r r));
    )^({n_1, dots, n_r})
  $
  to indicate that $Lambda$ is the set of all matrices
  $[T_(i j)]_(1 <= i, j <= r)$, where for each pair $(i, j)$, the matrix
  $T_(i j)$ ranges over all elements of $(frak(a)_(i j))^(n_i times n_j)$.
] <def:block-matrix-ring>

Now let $V$ be an $n$-dimensional right vector space over a skewfield $Omega$,
and set $End_Omega V = Hom_Omega (V, V)$. Thus $End_Omega V$ is the
$Omega$-endomorphism ring of $V$, and we shall view $V$ as an
$(End_Omega V, Omega)$-bimodule. Some of the calculations #source(363)which
follow are more easily understood by using matrices instead of linear
transformations. Once we pick an $Omega$-basis for $V$, we may identify $V$ with
the space $Omega^(n times 1)$ of all $n times 1$ column vectors over $Omega$.
This gives rise to an identification $End_Omega V = M_n (Omega)$, where the
matrices act from the left on the column vectors from $V$.

A _chain_#idx("chain in a vector space") in $V$ is a strictly decreasing
sequence
$
  E : V = V_0 > V_1 > dots.c > V_r = 0
$ <eq:chain>
of $Omega$-subspaces of $V$. We set
$
  n_i = dim_Omega V_(i-1) slash V_i, quad 1 <= i <= r,
$
and call the ordered $r$-tuple ${n_1, dots, n_r}$ the _invariants_#idx(
  "invariants of chain",
) of the chain $E$. Now define the _chain ring_#idx("chain ring") $O(E)$ by
$
  O(E) = {x in End_Omega V : x V_i subset V_i, quad 0 <= i <= r}.
$ <eq:chain-ring>

We may choose an $Omega$-basis of $V$ _adapted_ to the chain $E$, that is, the
first $n_1$ basis elements map onto a basis for $V_0 slash V_1$, the next $n_2$
elements onto a basis for $V_1 slash V_2$, and so on. Clearly
$n_1 + dots.c + n_r = n$, and the last $n_i + dots.c + n_r$ basis elements of
$V$ form a basis for the subspace $V_(i-1)$. Relative to this basis, we may
identify $O(E)$ with a subring of $M_n (Omega)$. It is easily seen that $O(E)$
consists of _all_ matrices
$
  mat(
    delim: "[",
    T_11, 0, 0, dots, 0;
    T_21, T_22, 0, dots, 0;
    dots.h, dots.h, dots.h, dots.h, dots.h;
    T_(r 1), T_(r 2), T_(r 3), dots, T_(r r);
  ),
$ <eq:chain-ring-matrices>
where for $1 <= j <= i <= r$, the matrix $T_(i j)$ ranges over all elements of
the additive group $Hom_Omega (V_(j-1) slash V_j, V_(i-1) slash V_i)$. Hence in
the notation of @def:block-matrix-ring, we may write
$
  O(E) = mat(
    delim: "[",
    (Omega), (0), (0), dots, (0);
    (Omega), (Omega), (0), dots, (0);
    dots.h, dots.h, dots.h, dots.h, dots.h;
    (Omega), (Omega), (Omega), dots, (Omega);
  )^({n_1, dots, n_r}).
$ <eq:chain-ring-blocks>
We collect some facts about chain rings.

#theorem[
  Let the chain $E$ in @eq:chain have invariants ${n_1, dots, n_r}$, and let
  $B = O(E)$ be its chain ring. Then
  + $
      rad B = {x in B : x V_i subset V_(i+1), 0 <= i <= r - 1}.
    $
    #source(364)In terms of the identification in @eq:chain-ring-blocks, $rad B$
    is given by
    $
      rad B = mat(
        delim: "[",
        (0), (0), (0), dots, (0);
        (Omega), (0), (0), dots, (0);
        dots.h, dots.h, dots.h, dots.h, dots.h;
        (Omega), (Omega), (Omega), dots, (0);
      )^({n_1, dots, n_r}),
    $ <eq:chain-ring-radical>
    that is, $rad B$ consists of all matrices in @eq:chain-ring-matrices in
    which each $T_(i i) = 0$, $1 <= i <= r$.
  + $
      B slash rad B tilde.equiv dsum_(i=1)^r End_Omega (V_(i-1) slash V_i)
      tilde.equiv dsum_(i=1)^r M_(n_i) (Omega).
    $
    The left $B$-modules ${V_(i-1) slash V_i : 1 <= i <= r}$ are a full set of
    non-isomorphic simple left $B$-modules.
  + For each $t$, $0 <= t <= r$, we have
    $
      V_t = (rad B)^t V, quad
      (rad B)^t = {x in B : x V_i subset V_(i+t), quad 0 <= i <= r},
    $
    where we interpret $V_s$ as 0 when $s >= r$.
] <th:chain-ring-properties>

#proof[
  Let
  $
    N = {x in B : x V_i subset V_(i+1), quad 0 <= i <= r - 1}.
  $
  Then $N$ is a two-sided ideal of $B$, and $N^r = 0$, whence $N subset rad B$.
  On the other hand, $N$ is the kernel of the ring epimorphism
  $
    B -> dsum_(i=1)^r End_Omega (V_(i-1) slash V_i).
  $
  Since the direct sum is a semisimple ring, we conclude from
  Exercise~@exc:semisimple-quotient-contains-radical that $N supset rad B$. This
  shows that $N = rad B$, and establishes (i) and the first statement in (ii).
  The second assertion in (ii) is an immediate consequence of the first.

  The easiest way of proving (iii) is by means of matrices. Choosing an
  $Omega$-basis for $V$ adapted to the chain $E$, we have identifications
  $
    V = mat(
      delim: "[",
      (Omega)^(n_1 times 1);
      dots.v;
      (Omega)^(n_r times 1);
    ),
    quad
    V_t = mat(
      delim: "[",
      (0);
      dots.v;
      (0);
      (Omega)^(n_(t+1) times 1);
      dots.v;
      (Omega)^(n_r times 1);
    ),
  $
  #source(365)for $0 <= t <= r$. The assertions in (iii) are then immediate
  consequences of the matrix expression for $rad B$ given in part (i). This
  completes the proof.
]

By way of illustration, we remark that when the chain $E$ is as fine as possible
(that is, each $n_i = 1$), then upon choosing an $Omega$-basis of $V$ adapted to
$E$, the chain ring $O(E)$ may be identified with the ring of all lower
triangular matrices in $M_n (Omega)$. Its radical consists of all those lower
triangular matrices with 0’s along the main diagonal. Up to conjugacy, this ring
$O(E)$ is the _smallest_ chain ring in $M_n (Omega)$. In this connection, see
Exercise~@exc:chain-rings-extremal.

Now let $B$ be any subring of $End_Omega V$, not necessarily a chain ring.
Setting $N = rad B$, we see that
$
  E_B : V > N V > N^2 V > dots.c > N^s V = 0
$
is a chain in $V$. Since $B subset End_Omega V$, it is clear that $s$ is the
least integer such that $N^s = 0$. We have
$
  B subset O(E_B), quad "and" quad rad B = N subset rad O(E_B).
$ <eq:subring-in-chain-ring>
We are thus led to partially order the set of subrings of $End_Omega V$, as
follows: given two subrings $B$, $B'$ of $End_Omega V$, we say that $B'$
_radically covers_#idx("radically cover") $B$ (notation: $B' succ B$) if
$
  B' supset B, quad "and" quad rad B' supset rad B.
$
Call $B$ an _extremal subring_#idx("extremal subring") of $End_Omega V$ if
$B' succ B$ implies that $B' = B$.

#lemma[
  The extremal subrings of $End_Omega V$ are precisely the chain rings.
] <lem:extremal-subrings-chain-rings>

#proof[
  If $B$ is extremal, then $B = O(E_B)$ by @eq:subring-in-chain-ring.
  Conversely, every chain ring $O(E)$ is an extremal subring, by
  Exercise~@exc:chain-rings-extremal.
]

We now turn to the analogues of these concepts for orders. Let $Lambda$,
$Lambda'$ denote $R$-orders in $A$. We say that $Lambda'$ _radically covers_
$Lambda$ (notation: $Lambda' succ Lambda$) if $Lambda' supset Lambda$ and
$rad Lambda' supset rad Lambda$. The order $Lambda$ is called _extremal_#idx(
  "extremal order",
) if $Lambda' succ Lambda$ implies that $Lambda' = Lambda$. Every maximal order
$Lambda$ is obviously extremal, since
$
  Lambda' succ Lambda => Lambda' supset Lambda => Lambda' = Lambda.
$
Our aim is to show that hereditary orders are the same as extremal orders. The
problem can be reduced to the central simple case; in this case, we shall show
that extremal orders correspond to extremal subrings of full matrix algebras
over a skewfield. This correspondence will enable us to determine the structure
of hereditary orders in central simple algebras. As a first step in this
program, we prove

#theorem[
  An $R$-order $Lambda$ in a separable $K$-algebra $A$ is extremal if and only
  if $O_l (rad Lambda) = Lambda$.
] <th:extremal-left-order-radical>

#proof[
  #source(366)Let $J = rad Lambda$; since $J supset P Lambda$, it is clear that
  $J$ is a full two-sided $Lambda$-lattice in $A$. Set
  $
    Gamma = O_l (J) = {x in A : x J subset J}.
  $
  Then $Gamma$ is an $R$-order in $A$, and $J subset Lambda subset Gamma$. For
  large $n$, $J^n subset P Lambda subset P Gamma$; hence $J subset rad Gamma$ by
  Exercise~@exc:radical-nilpotent-criterion, which shows that
  $Gamma succ Lambda$. Hence $Gamma = Lambda$ if $Lambda$ is an extremal order.

  Suppose conversely that $Gamma = Lambda$, and let us show that $Lambda$ is
  extremal. Let $Lambda' succ Lambda$, and set $J' = rad Lambda'$, so
  $J' supset J$. Since $P^r Lambda' subset J$ for some $r$, it follows that
  $(J')^s subset J$ for some $s$. Obviously $s > 0$, since otherwise
  $Lambda' subset J subset Lambda$, which is impossible. If $s >= 2$ then
  $
    (J')^(s-1) dot J subset (J')^(s-1) dot J' subset J,
  $
  so $(J')^(s-1) subset O_l (J) = Lambda$. Hence $(J')^(s-1)$ is a two-sided
  ideal in $Lambda$. But its $s$th power lies in $J$, whence also
  $(J')^(s-1) subset J$. Continuing in this way, we find eventually that
  $J' subset J$. Therefore $J' = J$, and so
  $
    Lambda = O_l (J) = O_l (J') supset Lambda',
  $
  whence $Lambda = Lambda'$. This completes the proof.
]

#corollary[
  Hereditary orders are extremal.
] <cor:hereditary-extremal>

#proof[
  Let $J = rad Lambda$, where $Lambda$ is hereditary. The last paragraph of the
  proof of @th:hereditary-radical-projective shows that $Lambda = O_l (J)$.
  Hence $Lambda$ is extremal.
]

In order to facilitate reduction of the discussion to the central simple case,
we now prove the local analogue of @th:maximal-orders-components for extremal
orders.

#theorem[
  Let $A = dsum_(i=1)^t A_i$ be the decomposition of the separable $K$-algebra
  $A$ into simple components ${A_i}$, and let $R_i$ be the integral closure of
  $R$ in the center of $A_i$. Then every extremal $R$-order $Lambda$ in $A$ is
  expressible as a direct sum $Lambda = dsum_(i=1)^t Lambda_i$, where each
  $Lambda_i$ is an extremal $R_i$-order in $A_i$. Conversely, every such direct
  sum $dsum Lambda_i$ is an extremal $R$-order in $A$.
] <th:extremal-decomposition>

#proof[
  Let $C = dsum_(i=1)^t R_i$, an $R$-order in the center of $A$. Then $C Lambda$
  is an $R$-order in $A$. Let $J = rad Lambda$; then $J^m subset P Lambda$ for
  some $m$, whence $(C J)^m subset P dot C Lambda$. Therefore
  $C J subset rad C Lambda$ by Exercise~@exc:radical-nilpotent-criterion, and so
  $C Lambda succ Lambda$. Since $Lambda$ is extremal, this gives
  $Lambda = C Lambda$. But $C Lambda = dsum_(i=1)^t R_i Lambda$, and for each
  $i$, $R_i Lambda$ is an extremal $R_i$-order in $A_i$. This completes the
  proof that each extremal order $Lambda$ #source(367)decomposes into a direct
  sum $dsum Lambda_i$, as claimed. The last assertion in the theorem is obvious,
  and the result is established.
]

Since we have shown that every hereditary order is extremal, the above
decomposition theorem is valid for all hereditary orders. In
@th:hereditary-center-order we shall obtain the global analogue of the above for
hereditary orders.

The preceding paragraph shows that the classification of hereditary orders can
always be reduced to the central simple case. The basic structure theorem for
this case is as follows:

#theorem(major: true)[
  Let $Lambda$ be an $R$-order in the central simple $K$-algebra $A$, where
  $A tilde.equiv M_n (D)$ and $D$ is a skewfield with center $K$. Let $Delta$ be
  the unique maximal $R$-order in $D$, and set $frak(p) = rad Delta$,
  $overline(Delta) = Delta slash frak(p)$. Then
  + $Lambda$ is hereditary if and only if $Lambda$ is an extremal order.
  + Given any extremal order $Lambda$ in $A$, there exist positive integers
    ${n_1, dots, n_r}$ with sum $n$, and there exists an identification
    $A = M_n (D)$, such that
    $
      Lambda = mat(
        delim: "[",
        (Delta), (frak(p)), (frak(p)), dots, (frak(p));
        (Delta), (Delta), (frak(p)), dots, (frak(p));
        (Delta), (Delta), (Delta), dots, (frak(p));
        dots.h, dots.h, dots.h, dots.h, dots.h;
        (Delta), (Delta), (Delta), dots, (Delta);
      )^({n_1, dots, n_r}),
    $ <eq:hereditary-standard-form>
    using the notation in @def:block-matrix-ring. Conversely, each such order
    $Lambda$ is extremal.
  + For the extremal order $Lambda$ in @eq:hereditary-standard-form, we have
    $
      rad Lambda = mat(
        delim: "[",
        (frak(p)), (frak(p)), (frak(p)), dots, (frak(p));
        (Delta), (frak(p)), (frak(p)), dots, (frak(p));
        (Delta), (Delta), (frak(p)), dots, (frak(p));
        dots.h, dots.h, dots.h, dots.h, dots.h;
        (Delta), (Delta), (Delta), dots, (frak(p));
      )^({n_1, dots, n_r}),
    $ <eq:hereditary-radical-form>
    and
    $
      Lambda slash rad Lambda
      tilde.equiv dsum_(i=1)^r M_(n_i) (overline(Delta)).
    $ <eq:hereditary-quotient-radical>
] <th:hereditary-structure>

#proof[
  Every hereditary order is extremal, by @cor:hereditary-extremal. To prove the
  converse, let $Lambda$ be an extremal order in $A$, and set $J = rad Lambda$.
  Let $Lambda subset Lambda'$ where $Lambda'$ is a maximal order in $A$ with
  radical $J'$. Then $Lambda + J' succ Lambda$ by
  Exercise~@exc:order-plus-radical, whence $Lambda + J' = Lambda$. Therefore
  $J' subset Lambda$, so $J' subset J$ by
  Exercise~@exc:radical-contained-in-order. We set
  #source(368)
  $
    overline(Lambda)' = Lambda' slash J', quad
    overline(Lambda) = Lambda slash J', quad
    overline(J) = J slash J'.
  $
  Then $overline(Lambda)$ is a subring of $overline(Lambda)'$, and
  $overline(J) = rad overline(Lambda)$ by Exercise~@exc:radical-of-quotient.

  We now use the results of @cor:complete-local-maximal-endomorphisms and
  @cor:complete-local-radical. We may find a right $Delta$-lattice $M$ such that
  $
    Lambda' = End_Delta M tilde.equiv M_n (Delta),
  $
  where $M tilde.equiv Delta^((n))$ is a $(Lambda', Delta)$-bimodule. Then
  $
    J' = End_Delta M frak(p) tilde.equiv M_n (frak(p)), quad
    overline(Lambda)' tilde.equiv End_(overline(Delta)) overline(M)
    tilde.equiv M_n (overline(Delta)),
  $
  where
  $
    overline(M) = M slash M frak(p) = M slash J' M
    tilde.equiv overline(Delta)^((n)).
  $

  Let $rho$ be the canonical map
  $
    rho : Lambda' -> Lambda' slash J' = M_n (overline(Delta)),
  $
  where we have identified $Lambda' slash J'$ with $M_n (overline(Delta))$. Then
  $overline(Lambda) = rho(Lambda)$, and we shall show that $overline(Lambda)$ is
  an extremal subring of $M_n (overline(Delta))$. For suppose that $B$ is any
  subring of $M_n (overline(Delta))$ which radically covers $overline(Lambda)$,
  and let $Lambda_0 = rho^(-1) (B)$, $J_0 = rad Lambda_0$. Then $Lambda_0$ is an
  $R$-order in $A$ such that $J' subset Lambda subset Lambda_0 subset Lambda'$,
  and so $J' subset J_0$ by Exercise~@exc:radical-contained-in-order. Hence
  Exercise~@exc:radical-of-quotient gives
  $
    J_0 slash J' = rad Lambda_0 slash J' = rad B supset rad overline(Lambda)
    = J slash J',
  $
  whence $J_0 supset J$. Therefore $Lambda_0 succ Lambda$, so
  $Lambda_0 = Lambda$ since $Lambda$ is an extremal order by hypothesis. This
  gives $B = overline(Lambda)$, and shows that $overline(Lambda)$ is an extremal
  subring of $M_n (overline(Delta))$.

  We may now use @lem:extremal-subrings-chain-rings to obtain the structure of
  $overline(Lambda)$. We form the chain $E$ in $overline(M)$, given by
  $
    E : overline(M) > J overline(M) > J^2 overline(M) > dots.c
    > J^r overline(M) = 0.
  $
  Note that $J^i overline(M) = overline(J)^i overline(M)$ for each $i$, since
  $Lambda'$ and $Lambda$ act on $overline(M)$ via the map $rho$. Let
  ${n_1, dots, n_r}$ be the invariants of the chain $E$, so by definition
  $
    n_i = dim_(overline(Delta)) J^(i-1) overline(M) slash J^i overline(M), quad
    1 <= i <= r.
  $
  Then @eq:chain-ring-blocks and @eq:chain-ring-radical give
  $
    overline(Lambda) = mat(
      delim: "[",
      (overline(Delta)), (0), dots, (0);
      (overline(Delta)), (overline(Delta)), dots, (0);
      dots.h, dots.h, dots.h, dots.h;
      (overline(Delta)), (overline(Delta)), dots, (overline(Delta));
    )^({n_1, dots, n_r}),
    quad
    overline(J) = mat(
      delim: "[",
      (0), (0), dots, (0);
      (overline(Delta)), (0), dots, (0);
      dots.h, dots.h, dots.h, dots.h;
      (overline(Delta)), (overline(Delta)), dots, (0);
    )^({n_1, dots, n_r}).
  $
  Since the map $rho$ is precisely "reduction $mod frak(p)$", and since
  $
    Lambda = rho^(-1) (overline(Lambda)), quad J = rho^(-1) (overline(J)),
    quad Lambda slash J tilde.equiv overline(Lambda) slash overline(J),
  $
  #source(369)we immediately obtain the asserted formulas
  @eq:hereditary-standard-form–@eq:hereditary-quotient-radical.

  At this stage we have proved the first two implications in the chain
  $
    Lambda " hereditary" => Lambda " extremal"
    => Lambda " satisfies " #[@eq:hereditary-standard-form]
    => Lambda " hereditary".
  $
  To complete the proof of the theorem, we need only show that an order $Lambda$
  given by @eq:hereditary-standard-form is necessarily hereditary. We set
  $
    Lambda' = M_n (Delta) supset Lambda, quad
    J' = rad Lambda' = M_n (frak(p)), quad
    rho : Lambda' -> Lambda' slash J',
  $
  as before. Since $rho$ is "reduction $mod frak(p)$", it is clear from
  @eq:hereditary-standard-form that $Lambda slash J'$ is a chain ring in the
  matrix algebra $M_n (overline(Delta))$. But then we know $rad Lambda slash J'$
  from @eq:chain-ring-radical. Since
  $rad Lambda = rho^(-1) {rad Lambda slash J'}$ by
  Exercise~@exc:radical-of-quotient, we immediately obtain formula
  @eq:hereditary-radical-form. The remaining formula
  @eq:hereditary-quotient-radical is then obvious.

  We are still trying to prove that the order $Lambda$ given by
  @eq:hereditary-standard-form is hereditary. Let $Lambda_0$ be the order in $A$
  defined by taking $n_1 = dots = n_r = 1$ in @eq:hereditary-standard-form.
  Since @eq:hereditary-radical-form gives us $rad Lambda_0$, it is easy to check
  that
  $
    rad Lambda_0 = Lambda_0 dot mat(
      delim: "[",
      0, 0, 0, dots, 0, pi_D;
      1, 0, 0, dots, 0, 0;
      0, 1, 0, dots, 0, 0;
      dots.h, dots.h, dots.h, dots.h, dots.h, dots.h;
      0, 0, 0, dots, 1, 0;
    ),
  $
  where $frak(p) = pi_D Delta = Delta pi_D$. Hence $rad Lambda_0$ is
  $Lambda_0$-projective, and thus $Lambda_0$ is hereditary by
  @th:hereditary-radical-projective. But $Lambda_0 subset Lambda subset A$, so
  $Lambda$ is also hereditary by @th:hereditary-overorder below. This completes
  the proof of the theorem.
]

When $Lambda$ is a hereditary order satisfying
@eq:hereditary-standard-form–@eq:hereditary-quotient-radical, we shall call $r$
the _type_#idx("type (of hereditary order)") of $Lambda$, and the ordered
$r$-tuple ${n_1, dots, n_r}$ the _invariants_#idx(
  "invariants of hereditary order",
) of $Lambda$. It is clear from @eq:hereditary-quotient-radical that a given
order $Lambda$ uniquely determines $r$ and the set of integers ${n_i}$. We shall
see in @cor:hereditary-invariants-unique below that $Lambda$ determines the
ordered $r$-tuple ${n_1, dots, n_r}$ uniquely, up to a cyclic permutation.
First, however, we shall obtain some consequences of the structure theorem
@th:hereditary-structure.

#corollary[
  Let $Lambda$ be a hereditary order (in a central simple $K$-algebra) of type
  $r$ and invariants ${n_1, dots, n_r}$. Keep the notation of
  @th:hereditary-structure and its proof. Then
  + $r$ is the unique positive integer such that $J^r M = M frak(p)$.
  + We have
    $
      Lambda = {x in A : x dot J^i M subset J^i M quad "for" 0 <= i <= r},
    $ <eq:hereditary-as-stabilizer>
    $
      J = {x in A : x dot J^i M subset J^(i+1) M quad "for" 0 <= i <= r - 1}.
    $ <eq:hereditary-radical-as-stabilizer>
  + $J^(r e) = pi Lambda$, where $e$ is the ramification index of $D$ over $K$.
  + $overline(Lambda)$ is a chain ring in $overline(Lambda)'$, corresponding to
    the chain
    #source(370)
    $
      E : overline(M) > J overline(M) > J^2 overline(M) > dots.c
      > J^r overline(M) = 0,
    $ <eq:hereditary-chain>
    with invariants given by
    $
      n_i = dim_(overline(Delta)) J^(i-1) overline(M) slash J^i overline(M),
      quad 1 <= i <= r.
    $
  + The modules ${J^(i-1) M slash J^i M : 1 <= i <= r}$ are a full set of
    non-isomorphic simple left $Lambda$-modules.
] <cor:hereditary-chain-properties>

#proof[
  _Step 1._ Let $tau$ be the canonical map
  $
    tau : M -> overline(M) = M slash M frak(p) = M slash J' M,
  $
  and set
  $
    overline(M)_i = J^i overline(M), quad M_i = tau^(-1) (overline(M)_i), quad
    0 <= i <= r.
  $
  Since $tau$ is a left $Lambda$-homomorphism, each $M_i$ is a
  $Lambda$-submodule of $M$. We claim that
  $
    M_i = J^i M quad "for" quad 0 <= i <= r, quad J^r M = M frak(p) = J' M.
  $ <eq:hereditary-chain-lattices>
  The easiest way to prove this is by a matrix calculation, as follows: choose a
  right $Delta$-basis for $M$ whose images in $overline(M)$ form a basis adapted
  to the chain $E$ in @eq:hereditary-chain. We may then write
  $
    M = Delta^((n)) = mat(
      delim: "[",
      (Delta)^(n_1 times 1);
      dots.v;
      (Delta)^(n_r times 1);
    ),
    quad
    overline(M) = overline(Delta)^((n)) = mat(
      delim: "[",
      (overline(Delta))^(n_1 times 1);
      dots.v;
      (overline(Delta))^(n_r times 1);
    ).
  $
  Therefore for $0 <= i <= r$,
  $
    overline(M)_i = J^i overline(M) = mat(
      delim: "[",
      (0)^(n_1 times 1);
      dots.v;
      (0)^(n_i times 1);
      (overline(Delta))^(n_(i+1) times 1);
      dots.v;
      (overline(Delta))^(n_r times 1);
    ),
    quad
    M_i = tau^(-1) (overline(M)_i) = mat(
      delim: "[",
      (frak(p))^(n_1 times 1);
      dots.v;
      (frak(p))^(n_i times 1);
      (Delta)^(n_(i+1) times 1);
      dots.v;
      (Delta)^(n_r times 1);
    ).
  $
  Since $J$ is given by @eq:hereditary-radical-form, we have
  #source(371)
  $
    J M = mat(
      delim: "[",
      (frak(p)), (frak(p)), dots, (frak(p));
      (Delta), (frak(p)), dots, (frak(p));
      dots.h, dots.h, dots.h, dots.h;
      (Delta), (Delta), dots, (frak(p));
    )
    mat(delim: "[", (Delta); (Delta); dots.v; (Delta))
    = mat(delim: "[", (frak(p)); (Delta); dots.v; (Delta)) = M_1.
  $
  Continuing in this manner, we easily obtain the formulas in
  @eq:hereditary-chain-lattices by induction on $i$. This establishes assertions
  (i) and (iv) of the corollary.

  _Step 2._ For the moment let $Lambda^*$ denote the order occurring on the
  right side of @eq:hereditary-as-stabilizer. Obviously $Lambda subset Lambda^*$
  since $Lambda dot J^i = J^i$ for each $i$. On the other hand, let
  $x in Lambda^*$; then $x M subset M$, so $x in End_Delta M = Lambda'$.
  Further, for $0 <= i <= r$, $x M_i subset M_i$ implies that
  $rho(x) overline(M)_i subset overline(M)_i$. Therefore
  $rho(x) in overline(Lambda)$, since $overline(Lambda)$ is the chain ring
  associated with the chain $E$ of @eq:hereditary-chain. Hence $x in Lambda$,
  which proves that $Lambda = Lambda^*$ and establishes
  @eq:hereditary-as-stabilizer. A similar argument proves
  @eq:hereditary-radical-as-stabilizer.

  Next, we have seen in the proof of @th:hereditary-structure that
  $Lambda slash J tilde.equiv overline(Lambda) slash overline(J)$, so the simple
  left $Lambda$-modules are the same as the simple left
  $overline(Lambda)$-modules, with $Lambda$ acting via the map
  $rho : Lambda -> overline(Lambda)$. By @th:chain-ring-properties[(ii)], the
  modules ${overline(M)_(i-1) slash overline(M)_i : 1 <= i <= r}$ are a full set
  of non-isomorphic simple left $overline(Lambda)$-modules. But $tau$ induces
  isomorphisms
  $
    M_(i-1) slash M_i tilde.equiv overline(M)_(i-1) slash overline(M)_i, quad
    1 <= i <= r.
  $
  and thus we have proved assertion (v) of the corollary.

  _Step 3._ Now let $e$ be the ramification index of $D$ over $K$ (see
  §~@sec:ramification-index-inertial-degree). Then
  $
    frak(p)^e = pi_D^e Delta = Delta pi_D^e = pi Delta.
  $
  Since $J^r M = M frak(p)$, we obtain
  $
    J^(r e) M = M frak(p)^e = pi M.
  $
  Therefore $T = pi^(-1) J^(r e)$ is a two-sided $Lambda$-ideal in $A$ such that
  $T M = M$ and $T J = J T$. Hence
  $
    T M_i = T dot J^i M = J^i dot T M = M_i, quad 0 <= i <= r.
  $
  It follows from @eq:hereditary-as-stabilizer that $T subset Lambda$, and we
  now show that $T = Lambda$. Indeed, $(T + J) slash J$ is a two-sided ideal of
  the semisimple artinian ring $Lambda slash J$. If it is a proper ideal, it is
  annihilated by some (nonzero) idempotent $epsilon$ in $Lambda slash J$. By
  @th:lifting-idempotents $epsilon$ is the image of some idempotent
  $a in Lambda$, and then obviously $a T subset J$. Therefore
  $
    a M_i = a T dot J^i M subset J^(i+1) M = M_(i+1), quad 0 <= i <= r - 1,
  $
  whence $a in J$ by @eq:hereditary-radical-as-stabilizer. This is impossible,
  since $rad Lambda$ contains no idempotents of $Lambda$. Therefore
  $T + J = Lambda$, whence $T = Lambda$ by @th:nakayama[Nakayama's Lemma].
  #source(372)We have thus proved that $pi^(-1) J^(r e) = Lambda$, whence
  $J^(r e) = pi Lambda$ as desired. This completes the proof of the corollary.
]

#remark(numbered: false)[
  The preceding proof shows that $J$ is an invertible
  $(Lambda, Lambda)$-bimodule, with inverse $pi^(-1) J^(r e - 1)$. It should be
  pointed out that the above argument yields another proof, independent of that
  given for @th:hereditary-radical-projective, of the implication
  $
    Lambda " hereditary" ==> rad Lambda " invertible".
  $
]

From the preceding results, we deduce

#theorem(major: true)[
  Keeping the hypotheses and notation of @cor:hereditary-chain-properties, let
  $
    Gamma_i = {x in A : x dot J^i M subset J^i M}, quad 0 <= i <= r - 1.
  $
  Then $Gamma_0, dots, Gamma_(r-1)$ are precisely the distinct maximal orders of
  $A$ containing $Lambda$, and
  $
    Lambda = Gamma_0 inter Gamma_1 inter dots.c inter Gamma_(r-1).
  $
  Furthermore, every indecomposable left $Lambda$-lattice is isomorphic to
  exactly one of the $Lambda$-lattices $M, J M, dots, J^(r-1) M$.
] <th:hereditary-maximal-overorders>

#proof[
  Suppose first that $L$ is any indecomposable left $Lambda$-lattice. The proof
  of @cor:global-lattices-projective shows that $K L$ must be a simple left
  $A$-module, and therefore $K L = K M$. Replacing $L$ by an isomorphic copy, we
  may assume that $L subset M$. Choose $t$ so that
  $
    L subset J^t M, quad L subset.not J^(t+1) M.
  $
  Since $J$ is invertible, it follows that if we set $L_1 = J^(-t) L$, then
  $
    L_1 subset M, quad L_1 subset.not J M.
  $
  Thus $(L_1 + J M) slash J M$ is a nonzero submodule of the simple
  $Lambda$-module $M slash J M$, whence $L_1 + J M = M$. Therefore $L_1 = M$,
  and so $L = J^t M$. Hence the modules ${J^t M}$ give all isomorphism classes
  of indecomposable left $Lambda$-lattices; each is obviously indecomposable,
  since $K dot J^t M$ is a simple $A$-module.

  We show now that $J^s M tilde.equiv J^t M$ as left $Lambda$-lattices if and
  only if $s equiv t (mod r)$. Any such isomorphism extends to an
  $A$-isomorphism $K M tilde.equiv K M$, hence must be given by right
  multiplication by some element $d in D$. Writing $d = u dot pi_D^k$, where
  $u in u(Delta)$ and $pi_D$ is a prime element of $Delta$, it follows that
  $J^s M tilde.equiv J^t M$ if and only if $J^s M = J^t M dot pi_D^k$ for some
  $k$. Since $M pi_D = J^r M$, this occurs if and only if $r | (s - t)$, and the
  second assertion of the theorem is proved.

  For each integer $t$, set $Gamma_t = {x in A : x dot J^t M subset J^t M}$. Now
  $J^t M$ is a right $Delta$-lattice such that
  $K dot J^t M = K dot Delta^((n))$, whence $J^t M tilde.equiv Delta^((n))$ by
  Exercise~@exc:skewfield-order-lattices-free. #source(373)Since
  $Gamma_t = End_Delta J^t M$ it follows from
  @cor:complete-local-maximal-endomorphisms that $Gamma_t$ is a maximal order.
  Clearly $Gamma_s = Gamma_t$ whenever $s equiv t (mod r)$. Conversely, if
  $Gamma_s = Gamma_t$ then $J^s M$ and $J^t M$ are a pair of
  $(Gamma_t, Delta)$-bimodules; hence by @th:morita-equivalence
  $J^s M = J^t M dot frak(p)^k$ for some $k$, whence $r | (s - t)$. This shows
  that $Gamma_0, dots, Gamma_(r-1)$ are distinct orders containing $Lambda$.
  Their intersection is $Lambda$, by @eq:hereditary-as-stabilizer. Finally, let
  $Gamma$ be any maximal order of $A$ containing $Lambda$. Every indecomposable
  left $Gamma$-lattice is also an indecomposable left $Lambda$-lattice, hence
  may be taken to be one of ${J^i M : 0 <= i <= r - 1}$. Therefore $Gamma$ must
  coincide with one of the orders $Gamma_0, dots, Gamma_(r-1)$, and the theorem
  is established.
]

#corollary[
  Keep the above notation and hypotheses. Then $Lambda$ uniquely determines the
  ordered $r$-tuple ${n_1, dots, n_r}$ of invariants, up to cyclic permutation.
] <cor:hereditary-invariants-unique>

#proof[
  Let $Lambda subset Lambda' = End_Delta M$, and let us show that the invariants
  ${n_1, dots, n_r}$ are unaffected by using $N$ in place of $M$, where $N$ is
  another $Delta$-lattice such that $Lambda' = End_Delta N$. By
  @th:morita-equivalence we may write $N = M frak(p)^k = M pi_D^k$ for some
  integer $k$. It is then easily verified that the invariants computed using $N$
  are the same as those obtained from $M$.

  On the other hand, if $Gamma_t$ is one of the maximal orders containing
  $Lambda$, then we have seen that $Gamma_t = End_Delta J^t M$. Thus we obtain
  invariants ${n'_i}$, where
  $
    n'_i = dim_(overline(Delta)) J^(i-1) dot J^t overline(M) slash J^i dot J^t
    overline(M) = n_(i+t), quad 1 <= i <= r,
  $
  and where the subscript $i + t$ is read $mod r$. This shows that all cyclic
  permutations of ${n_1, dots, n_r}$ can arise as invariants, and these are the
  only possibilities.
]

Returning to the general case, we have

#theorem[
  Let $Lambda$ be an $R$-order in a separable $K$-algebra. Then $Lambda$ is
  hereditary if and only if $Lambda$ is extremal.
] <th:hereditary-iff-extremal>

#proof[
  By @cor:hereditary-extremal, hereditary orders are extremal. Conversely, any
  extremal order $Lambda$ can be decomposed as $Lambda = dsum Lambda_i$ by
  @th:extremal-decomposition. But then each $Lambda_i$ is hereditary by
  @th:hereditary-structure, whence so is $Lambda$.
]

If we assume merely that $R$ is a discrete valuation ring, not necessarily
complete, then the structure theorem @th:hereditary-structure and its
consequences @cor:hereditary-chain-properties–@th:hereditary-maximal-overorders
remain valid whenever the $P$-adic completion $D_P$ is a skewfield.

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $L$ be a left ideal of the $R$-order $Lambda$. Show that
  $
    L^m subset P Lambda "for some" m <==> L subset rad Lambda.
  $
  #source(374)#hint[@exc:radical-nilpotent-criterion][By
    @th:radical-local-algebra,
    $(rad Lambda)^n subset P Lambda subset rad Lambda$ for all sufficiently
    large $n$. Hence
    $
      L subset rad Lambda ==> L^n subset P Lambda.
    $
    Conversely, suppose that $L^m subset P Lambda$ for some $m$. Then $L Lambda$
    is a two-sided ideal of $Lambda$, and
    $
      (L Lambda)^m = (L Lambda)(L Lambda) dots.c (L Lambda) subset L^m Lambda
      subset P Lambda subset rad Lambda.
    $
    Hence $L Lambda subset rad Lambda$ by Exercise~@exc:ideal-in-radical.]
  <hint:radical-nilpotent-criterion>
] <exc:radical-nilpotent-criterion>

#exercise[
  Let $Lambda subset Lambda'$ be $R$-orders in $A$. Show that
  $Lambda + rad Lambda'$ is an $R$-order in $A$ whose radical contains
  $rad Lambda$.
  #hint[@exc:order-plus-radical][Let $J = rad Lambda$, $J' = rad Lambda'$.
    Clearly $Lambda + J'$ is an order, and we must show that
    $J subset rad (Lambda + J')$. For large $m$,
    $
      (J + J')^m subset J^m + J' subset P Lambda + J' subset P Lambda' + J',
    $
    and
    $
      (P Lambda' + J')^m subset P Lambda' + J'^m subset P Lambda'.
    $
    Thus
    $
      (J + J')^(m^3) subset P^m Lambda' subset P Lambda
      subset P(Lambda + J')
    $
    for large $m$, whence $J + J' subset rad (Lambda + J')$ by
    Exercise~@exc:radical-nilpotent-criterion.]
  <hint:order-plus-radical>
] <exc:order-plus-radical>

#exercise[
  Let $Lambda subset Lambda'$ be $R$-orders in $A$, and suppose that
  $rad Lambda' subset Lambda$. Show that $rad Lambda' subset rad Lambda$.
  #hint[@exc:radical-contained-in-order][Let $J' = rad Lambda'$. As in
    Exercise~@exc:order-plus-radical, we get $J'^r subset P Lambda$ for large
    $r$. Since $J'$ is an ideal of $Lambda$, it follows from
    Exercise~@exc:radical-nilpotent-criterion that $J' subset rad Lambda$.]
  <hint:radical-contained-in-order>
] <exc:radical-contained-in-order>

#exercise[
  Let $N$ be a two-sided ideal of the $R$-order $Lambda$ contained in
  $rad Lambda$. Prove that
  $
    (rad Lambda) slash N = rad (Lambda slash N).
  $
  #hint[@exc:radical-of-quotient][Let $J = rad Lambda$,
    $overline(J) = J slash N$, $overline(Lambda) = Lambda slash N$. Then
    $overline(Lambda) slash overline(J) tilde.equiv Lambda slash J$, a
    semisimple ring. Hence $overline(J) supset rad overline(Lambda)$ by
    Exercise~@exc:semisimple-quotient-contains-radical. On the other hand,
    $psi : Lambda -> overline(Lambda)$ is epic, so
    $overline(J) = psi(J) subset rad overline(Lambda)$ by
    @th:radical-epimorphism.]
  <hint:radical-of-quotient>
] <exc:radical-of-quotient>

#exercise[
  Let $E$, $E'$ be a pair of chains in the $Omega$-space $V$, and define the
  chain rings $O(E)$, $O(E')$ as in @eq:chain-ring. Prove
  + $O(E) supset O(E')$ if and only if $E'$ is a refinement of $E$.
  + $O(E) succ O(E')$ if and only if $E = E'$.
  + $O(E)$ is an extremal subring of $End_Omega V$.

  #hint[@exc:chain-rings-extremal][To prove (i) and (ii), consider the matrix
    representations @eq:chain-ring-blocks and @eq:chain-ring-radical of the
    rings $O(E)$, $O(E')$ and their radicals. To prove (iii), let $O(E)$ be
    given, and consider all subrings $B$ of $M_n (Omega)$ such that
    $B succ O(E)$. We may choose a maximal element $B'$ relative to this partial
    ordering. Then $B'$ is an extremal subring of $M_n (Omega)$, whence
    $B' = O(E_(B'))$ by @lem:extremal-subrings-chain-rings. But then
    $O(E_(B')) succ O(E)$, so by (ii) we have $B' = O(E_(B')) = O(E)$.]
  <hint:chain-rings-extremal>
] <exc:chain-rings-extremal>

In Exercises~@exc:hereditary-invertible-bimodules–@exc:hereditary-factorization,
we keep the hypotheses and notation of @cor:hereditary-chain-properties and
@th:hereditary-maximal-overorders and their proofs.

#exercise[
  Show that every invertible $(Lambda, Lambda)$-bimodule in $A$ is a power of
  $rad Lambda$, and deduce that $Picent Lambda$ is cyclic of order $r e$.
  #hint[@exc:hereditary-invertible-bimodules][Let $T$ be an invertible bimodule;
    then $T J T^(-1) = rad (T Lambda T^(-1)) = rad Lambda = J$, so $T J = J T$.
    Let $U = J^k T$ with $k$ chosen so that $U subset Lambda$, $U subset.not J$.
    Then $J M < (U + J) M subset M$, the first inclusion being proper #source(
      375,
    )since otherwise $U subset J$. Hence $(U + J) M = M$. Now use the argument
    in Step~3 of the proof of @cor:hereditary-chain-properties to deduce that
    $U = Lambda$.]
  <hint:hereditary-invertible-bimodules>
] <exc:hereditary-invertible-bimodules>

#exercise[
  Let $Lambda$ be a hereditary order of type $r$. Prove
  + There are exactly $2^r - 1$ distinct orders in $A$ containing $Lambda$,
    namely the intersections of the orders in each non-empty subset of
    ${Gamma_0, dots, Gamma_(r-1)}$.
  + The maximal possible length of a chain of orders
    $
      Lambda < Lambda_1 < dots.c < Lambda_s
    $
    in $A$ is $r$ itself.
  + If $r > 1$, there are precisely $r$ distinct orders $Lambda_1$ with
    $Lambda_1 > Lambda$, such that there is no order properly between $Lambda_1$
    and $Lambda$.
] <exc:hereditary-overorders-count>

#exercise[
  For the order $Lambda$ in @eq:hereditary-standard-form, describe explicitly
  those maximal orders containing $Lambda$.
] <exc:hereditary-maximal-overorders-explicit>

#exercise[
  For $0 <= t <= r - 1$, let
  $
    J_t = {x in Lambda : x dot J^t M subset J^(t+1) M}.
  $
  Show that ${J_0, dots, J_(r-1)}$ are the distinct maximal two-sided ideals of
  $Lambda$, and that $J_t supset rad Gamma_t$. Prove that
  $
    Lambda slash J tilde.equiv dsum_(t=0)^(r-1) Lambda slash J_t.
  $
  For each $t$, calculate the _conductor_#idx("conductor")
  ${x in A : Gamma_t dot x subset Lambda}$.
] <exc:hereditary-maximal-ideals>

#exercise[
  Prove that $J^r Lambda' = J'$, where $Lambda'$ is a maximal order containing
  $Lambda$, and $J' = rad Lambda'$.
  #hint[@exc:hereditary-radical-power][$J^r Lambda'$ is a two-sided ideal of
    $Lambda'$, hence is a power of $J'$. Now use @eq:hereditary-chain-lattices.]
  <hint:hereditary-radical-power>
] <exc:hereditary-radical-power>

#exercise[
  Show that the formula
  $
    J' = J^r Lambda' = L_r dot L_(r-1) dots.c L_2 dot L_1, quad "where" quad
    L_i = J^i Lambda' J^(-(i-1)),
  $
  expresses $J'$ as a proper product of $r$ integral ideals $L_r, dots, L_1$.
  Prove that
  $
    Lambda = inter.big_(i=1)^r O_l (L_i),
  $ <eq:hereditary-intersection-left-orders>
  and that the chain @eq:hereditary-chain for $Lambda$ is just
  $
    overline(M) > L_1 overline(M) > L_2 L_1 overline(M) > dots.c
    > (L_r dots.c L_1) overline(M) = 0.
  $ <eq:hereditary-factorization-chain>
  Show conversely that starting with any maximal order $Lambda'$ and any proper
  factorization
  $
    rad Lambda' = L_r dot L_(r-1) dots.c L_2 dot L_1
  $
  into integral ideals, the order $Lambda$ given by
  @eq:hereditary-intersection-left-orders is hereditary and corresponds to the
  chain @eq:hereditary-factorization-chain.
] <exc:hereditary-factorization>

#exercise[
  Give an example of two maximal orders $Lambda_1$, $Lambda_2$ in a central
  simple $K$-algebra, for which $Lambda_1 inter Lambda_2$ is _not_ hereditary.
] <exc:maximal-intersection-not-hereditary>

#exercise[
  Let $Lambda_1$, $Lambda_2$ be hereditary $R$-orders in the central simple
  $K$-algebra $A$. Show that there exists a full $R$-lattice $Y$ in $A$ such
  that
  $
    Lambda_1 = O_l (Y), quad Lambda_2 = O_r (Y),
  $
  if and only if $Lambda_1$ and $Lambda_2$ are of the same type.
] <exc:hereditary-same-type>
