#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/01-06-radicals-of-rings.typ": lifted-pair

== Maximal orders (local case) <sec:maximal-orders-local-case>

Keeping the notation introduced at the beginning of this chapter, let $R$
#source(184)be a discrete valuation ring, not necessarily complete. Let $hat(R)$
denote the $P$-adic completion of $R$, and $hat(K)$ the quotient field of
$hat(R)$. Given any separable $K$-algebra $B$, we may form the $hat(K)$-algebra
$hat(B) = hat(K) times.o_K B$, which is a separable $hat(K)$-algebra by
Exercise~@exc:separable-base-change. Of course, when $B$ is a central simple
$K$-algebra, we know from @cor:central-simple-extension that $hat(B)$ is a
central simple $hat(K)$-algebra. However, if $B$ is merely assumed separable
over $K$, then it may well happen that $hat(B)$ will have more simple components
than $B$. This may occur even when $B$ is a field (see
Exercise~@exc:separable-times-semisimple, for example). Even in the case where
$B$ is central simple over $K$, the full matrix algebras $B, hat(B)$ may consist
of different size matrices. Despite these precautionary remarks, however, we can
obtain results on $R$-orders in $B$ by using the theorems in
§~@sec:maximal-orders-complete-local-case on $hat(R)$-orders in $hat(B)$.

If $Gamma$ is any $R$-order in $B$, then setting
$hat(Gamma) = hat(R) times.o_R Gamma$, we obtain an $hat(R)$-order $hat(Gamma)$
in $hat(B)$. If $M$ is any $Gamma$-module, then $hat(M) = hat(R) times.o_R M$ is
a $hat(Gamma)$-module. We shall use such notation hereafter without further
comment. By @th:completion-maximal-order, $Gamma$ is a maximal order in $B$ if
and only if $hat(Gamma)$ is a maximal order in $hat(B)$.

#theorem[
  Every maximal $R$-order $Gamma$ in a separable $K$-algebra $B$ is left and
  right hereditary.
] <th:local-maximal-hereditary>

#proof[
  By @th:maximal-orders-components, the maximal $hat(R)$-order $hat(Gamma)$ is
  expressible as a ring direct sum $dsum Lambda_i$ of maximal $R_i$-orders in
  central simple algebras, where each $R_i$ is a complete discrete valuation
  ring in the center of some simple component of $hat(B)$. Each of these direct
  summands $Lambda_i$ is hereditary by @th:complete-local-maximal-orders, and
  thus $hat(Gamma)$ itself is hereditary. Therefore also $Gamma$ is hereditary,
  by §~@ss:localization-at-prime-ideals.
]

#theorem[
  Let $Lambda$ be any $R$-algebra, finitely generated as $R$-module, and let
  $overline(Lambda) = Lambda slash pi Lambda$.
  + For each $s >= 1$, there is a ring isomorphism
    $
      Lambda slash pi^s Lambda tilde.equiv hat(Lambda) slash pi^s hat(Lambda).
    $
  + There are ring isomorphisms
    $
      Lambda slash rad Lambda tilde.equiv overline(Lambda) slash
      rad overline(Lambda) tilde.equiv hat(Lambda) slash rad hat(Lambda).
    $
  + Let $M, N$ be finitely generated left $Lambda$-modules. Then
    $M tilde.equiv N$ as $Lambda$-modules if and only if
    $hat(M) tilde.equiv hat(N)$ as $hat(Lambda)$-modules.
] <th:local-completion-comparison>

#proof[
  Assertion (i) follows immediately from
  Exercise~@exc:completion-residue-modules. Taking $s = 1$ in (i), we have
  $overline(Lambda) tilde.equiv hat(Lambda) slash pi hat(Lambda)$. We then
  obtain (ii) by applying @th:radical-local-algebra twice, once for the
  $R$-order $Lambda$ and once for the $hat(R)$-order $hat(Lambda)$.

  To prove (iii), we note that if $M tilde.equiv N$, then obviously
  $hat(M) tilde.equiv hat(N)$. Conversely, let
  $phi : hat(M) tilde.equiv hat(N)$, and let $psi = phi^(-1)$. Since $hat(R)$ is
  a flat $R$-module (see @cor:completion-faithfully-flat or
  Exercise~@exc:completion-faithfully-flat), it follows at once by
  @th:change-of-rings-iso that
  $
    hat(R) times.o_R Hom_Lambda (M, N)
    tilde.equiv Hom_(hat(Lambda)) (hat(M), hat(N)).
  $
  #source(185)Thus we may view $Hom_(hat(Lambda)) (hat(M), hat(N))$ as the
  $P$-adic completion of $Hom_Lambda (M, N)$. But $Hom_Lambda (M, N)$ is dense
  in its completion (see §~@sec:completions-and-valuations, or
  @th:completion-of-module), and so we can find an $f in Hom_Lambda (M, N)$ such
  that
  $
    f equiv phi (mod pi dot Hom_(hat(Lambda)) (hat(M), hat(N))).
  $
  Likewise, we may choose $g in Hom_Lambda (N, M)$ such that
  $g equiv psi (mod pi)$. Then $g f in Hom_Lambda (M, M)$ is such that
  $
    m - (g f) m in pi hat(M), quad m in M.
  $
  However, $M inter pi hat(M) = pi M$ by
  Exercise~@exc:completion-residue-modules, and thus $m - (g f) m in pi M$ for
  all $m in M$. This gives
  $
    M = (g f) M + pi M.
  $
  But $rad R = pi R$, and $M$ is a finitely generated $R$-module, so by
  @th:nakayama[Nakayama's Lemma] it follows from the above that $M = (g f) M$.
  Therefore $g f$ is a $Lambda$-automorphism of $M$, by
  @th:surjective-endomorphism-noetherian. Likewise, $f g$ is a
  $Lambda$-automorphism of $N$. Thus both $f$ and $g$ are isomorphisms, which
  shows that $M tilde.equiv N$, and completes the proof of the theorem.
]

#theorem(major: true)[
  Let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$. Then
  $Lambda$ has a unique maximal two-sided ideal $frak(P)$, given by
  $frak(P) = Lambda inter rad hat(Lambda)$. Then $rad Lambda = frak(P)$, and
  every nonzero two-sided ideal of $Lambda$ is a power of $frak(P)$. Further,
  $rad hat(Lambda)$ is the $P$-adic completion of $rad Lambda$.
] <th:local-maximal-two-sided-ideals>

#proof[
  Since $hat(Lambda)$ is a maximal $hat(R)$-order in the central simple
  $hat(K)$-algebra $hat(A)$, the ring $hat(Lambda) slash rad hat(Lambda)$ is
  simple. Hence also $Lambda slash rad Lambda$ is simple, by
  @th:local-completion-comparison. But every maximal two-sided ideal of $Lambda$
  contains $rad Lambda$ by @cor:maximal-ideal-contains-radical, and thus
  $rad Lambda$ is the unique maximal two-sided ideal of $Lambda$. Furthermore,
  @th:local-completion-comparison[(ii)] implies at once that
  $
    rad Lambda = Lambda inter rad hat(Lambda), quad
    hat(R) times.o_R rad Lambda = rad hat(Lambda).
  $

  Next, since $A$ is simple, every nonzero two-sided ideal $M$ of $Lambda$ is
  such that $K M = A$. Thus $M supset pi^s Lambda$ for some $s$, and hence $M$
  is the inverse image of a two-sided ideal of $Lambda slash pi^s Lambda$. But
  $Lambda slash pi^s Lambda tilde.equiv hat(Lambda) slash pi^s hat(Lambda)$, and
  all two-sided ideals of $hat(Lambda) slash pi^s hat(Lambda)$ are images of
  powers of $rad hat(Lambda)$. It follows at once that $M$ itself is a power of
  $frak(P)$, as claimed. This completes the proof of the theorem.
]

We next give a criterion, due to Auslander–Goldman [@bib:Auslander1960a], for an
order to be maximal.

#theorem[
  Let $Lambda$ be an $R$-order in the central simple $K$-algebra $A$. Then
  $Lambda$ is maximal if and only if $Lambda$ is hereditary, and $rad Lambda$ is
  its unique maximal two-sided ideal.
] <th:auslander-goldman-local-criterion>

#proof[
  #source(186)Maximal orders have the indicated properties, by
  @th:local-maximal-hereditary and @th:local-maximal-two-sided-ideals.
  Conversely, let $Lambda$ be hereditary, with unique maximal two-sided ideal
  $rad Lambda$, and let $Gamma$ be an order properly containing $Lambda$. Then
  $Gamma$ is a left $Lambda$-lattice, hence is a finitely generated projective
  left $Lambda$-module by @cor:hereditary-lattices-projective. It follows then
  from @th:derived-context-epic that the map
  $
    mu : Hom_Lambda (Gamma, Lambda) times.o_Lambda Gamma
    -> Hom_Lambda (Gamma, Gamma)
  $
  is epic, where
  $
    mu(f times.o gamma) = (f, gamma), quad
    gamma' (f, gamma) = [gamma', f] gamma,
  $
  and $[gamma', f]$ is $f$ evaluated at $gamma'$. Suppose that
  $mu{sum f_i times.o gamma_i} = 1$. Then $sum gamma (f_i, gamma_i) = gamma$ for
  all $gamma in Gamma$, that is,
  $
    sum [gamma, f_i] gamma_i = gamma, quad gamma in Gamma.
  $

  Now consider the trace ideal $T$ of the left $Lambda$-module $Gamma$ (see
  @eq:trace-ideal). Then $T$ is the two-sided ideal of $Lambda$ spanned by
  $
    {[gamma, f] : gamma in Gamma, f in Hom_Lambda (Gamma, Lambda)},
  $
  so the above equation implies that $T Gamma = Gamma$. Let us show that $T$ is
  a proper ideal of $Lambda$. If $T = Lambda$, then $Gamma$ is a progenerator of
  $lmodule(Lambda, cal(M))$. This gives (by @th:morita-equivalence)
  $
    Lambda = Hom_Omega (Gamma, Gamma), quad "where" quad
    Omega = Hom_Lambda (Gamma, Gamma),
  $
  and where $lmodule(Lambda, Gamma)_Omega$ is viewed as a bimodule. But then
  $Omega = Gamma$, since every $Lambda$-endomorphism of $lmodule(Lambda, Gamma)$
  is given by right multiplication by an element of $Gamma$. Therefore we obtain
  $Lambda = Hom_Omega (Gamma, Gamma) = Gamma$, a contradiction.

  We have now shown that $T$ is a proper ideal of $Lambda$, and thus $T$ is
  contained in the unique maximal two-sided ideal $rad Lambda$ of $Lambda$.
  Since $T Gamma = Gamma$, it follows that $(rad Lambda) Gamma = Gamma$, which
  is impossible by @th:nakayama[Nakayama's Lemma]. This shows that $Lambda$ is a
  maximal order, and completes the proof of the theorem.
]

We are going to show that maximal $R$-orders in separable $K$-algebras are
principal ideal rings, that is, every one-sided ideal is principal.
@th:maximal-orders-components[Theorem] and
@th:local-completion-comparison[Theorem] will enable us to reduce this question
to the case of maximal orders in central simple algebras. The key to the proof
is the fact that such an order $Lambda$ is a _primary ring_#idx("primary ring"),
that is, $Lambda slash rad Lambda$ is a simple artinian ring. We begin with a
result on primary algebras.

#theorem[
  Let $B$ be a primary finite dimensional algebra over a field $k$, and let
  $M, N$ be finitely generated projective left $B$-modules. Then
  $M tilde.equiv N$ if and only if $(M : k) = (N : k)$.
] <th:primary-algebra-projectives>

#proof[
  Let $overline(B) = B slash rad B$, a simple artinian ring, and let $b in B$
  map onto $overline(b) in overline(B)$. #source(187)Suppose that
  $
    B = B e_1 plus.o dots.c plus.o B e_n
  $
  is a decomposition of $B$ into a direct sum of indecomposable left ideals,
  where the ${e_i}$ are primitive idempotents in $B$. By
  @th:artinian-decomposition, $B e_i tilde.equiv B e_j$ if and only if
  $overline(B) overline(e)_i tilde.equiv overline(B) overline(e)_j$, and the
  modules ${overline(B) overline(e)_i}$ are minimal left ideals of
  $overline(B)$. Since $overline(B)$ is simple artinian, the
  ${overline(B) overline(e)_i}$ are mutually isomorphic. Therefore
  $B e_i tilde.equiv B e_1$ for all $i$. But $M$ and $N$ are direct summands of
  $B^((s))$ for some $s$, whence by the Krull–Schmidt Theorem
  (Exercise~@exc:krull-schmidt), both $M$ and $N$ are direct sums of copies of
  $B e_1$. Hence $M tilde.equiv N$ if and only if $M$ and $N$ have the same
  $k$-dimension.
]

We need one more preliminary result:

#theorem[
  Let $Lambda$ be any $R$-order in a finite dimensional $K$-algebra $K Lambda$,
  and let $M, N$ be projective left $Lambda$-lattices. Set
  $overline(Lambda) = Lambda slash pi Lambda$, $overline(M) = M slash pi M$,
  $overline(N) = N slash pi N$. Then $M tilde.equiv N$ as $Lambda$-modules if
  and only if $overline(M) tilde.equiv overline(N)$ as
  $overline(Lambda)$-modules.
] <th:projective-lattices-reduction>

#proof[
  Clearly $M tilde.equiv N$ implies that $overline(M) tilde.equiv overline(N)$.
  Conversely, let $phi : overline(M) tilde.equiv overline(N)$ be a
  $overline(Lambda)$-isomorphism. Since both $M$ and $N$ are
  $Lambda$-projective, we may find $Lambda$-homomorphisms $alpha, beta$ lifting
  $phi, phi^(-1)$, respectively, making the following diagram commute:
  $
    #lifted-pair(
      ($M$, $N$),
      ($overline(M)$, $overline(N).$),
      ($alpha$, $beta$),
      ($phi$, $phi^(-1)$),
    )
  $
  For $m in M$, we have $(beta alpha) m - m in pi M$. Hence
  $M = beta alpha M + pi M$, so $M = beta alpha M$ by @th:nakayama[Nakayama's
    Lemma]. Then $beta alpha$ is an automorphism of $M$ by
  @th:surjective-endomorphism-noetherian. Likewise, $alpha beta$ is an
  automorphism of $N$, and so $alpha : M tilde.equiv N$, as desired.
]

There is a generalization of the above theorem, in which the hypothesis on $M$
and $N$ is dropped. The general version states: If $K Lambda$ is $K$-separable,
then there exists a positive integer $q$ depending on $Lambda$, such that for
any pair of $Lambda$-lattices $M, N$, we have $M tilde.equiv N$ if and only if
$M slash pi^q M tilde.equiv N slash pi^q N$. Indeed, $q$ may be chosen so that
$pi^(q-1) R$ is the Higman ideal of $Lambda$ (see Curtis–Reiner
[@bib:Curtis1962, Th.~76.8], where the Higman ideal is denoted by $i(Lambda)$).

We are now ready to generalize
@th:complete-local-maximal-orders–@th:left-right-orders-maximal to the present
case, in which $R$ need not be complete.

#theorem(major: true)[
  #source(188)Let $Lambda$ be a maximal $R$-order in a central simple
  $K$-algebra $A$.
  + Let $M$ and $N$ be left $Lambda$-lattices. Then $M tilde.equiv N$ if and
    only if $M$ and $N$ have the same $R$-rank.
  + Every one-sided ideal of $Lambda$ is principal.
  + Every maximal $R$-order in $A$ is a conjugate $u Lambda u^(-1)$ of $Lambda$,
    where $u in u(A)$.
  + Let $hat(A) = hat(K) times.o_K A tilde.equiv M_t (E)$, where $E$ is a
    skewfield with center $hat(K)$, and let $Omega$ be the unique maximal
    $hat(R)$-order in $E$. Then
    $
      Lambda slash rad Lambda tilde.equiv M_t (Omega slash rad Omega),
    $
    and $Omega slash rad Omega$ is a skewfield.
] <th:local-hereditary-principal>

#proof[
  Since $Lambda$ is hereditary, $M$ is $Lambda$-projective by
  @cor:hereditary-lattices-projective. Thus $overline(M) = M slash pi M$ is
  $overline(Lambda)$-projective, since if $M | Lambda^((r))$ then
  $overline(M) | overline(Lambda)^((r))$. Now let $M, N$ be any left
  $Lambda$-lattices. Then by @th:projective-lattices-reduction,
  $M tilde.equiv N$ if and only if $overline(M) tilde.equiv overline(N)$ as
  $overline(Lambda)$-modules. Since $hat(Lambda) slash rad hat(Lambda)$ is a
  simple artinian ring by @cor:complete-local-radical, it follows from
  @th:local-completion-comparison that $overline(Lambda)$ is a primary ring.
  Hence by @th:primary-algebra-projectives,
  $overline(M) tilde.equiv overline(N)$ if and only if
  $(overline(M) : overline(R)) = (overline(N) : overline(R))$. Finally, we note
  that $(overline(M) : overline(R)) = rank_R M$. This proves that
  $M tilde.equiv N$ if and only if $M$ and $N$ have the same $R$-rank.

  Suppose next that $M$ is a left ideal of $Lambda$. Then $K M$ is a left ideal
  of the simple artinian ring $A$, whence $K M = A e = K dot Lambda e$ for some
  idempotent $e in A$. Hence $Lambda e tilde.equiv M$ by (i); if this
  isomorphism maps $e$ onto $m$, then $M = Lambda m$. This completes the proof
  of (ii). It should be pointed out that this proof is completely independent of
  that given for the corresponding statement in
  @th:complete-local-maximal-orders[(iii)], and so constitutes another proof of
  that statement.

  The argument in @th:complete-local-maximal-orders which proves that every
  maximal order is conjugate to $Lambda$, carries over unchanged to the present
  case. It remains for us to prove (iv). Keeping the notation of (iv), we showed
  in @cor:complete-local-radical that
  $
    hat(Lambda) slash rad hat(Lambda) tilde.equiv M_t (Omega slash rad Omega).
  $
  Thus the desired formula for $Lambda slash rad Lambda$ holds by virtue of
  @th:local-completion-comparison. This completes the proof of the theorem.
]

#remark(kind: "Remarks")[
  + The integer $t$ occurring in @th:local-hereditary-principal[(iv)] is called
    the _capacity_#idx("capacity") of $rad Lambda$. If $A tilde.equiv M_r (D)$,
    where $D$ is a skewfield, and if
    $
      hat(D) = hat(K) times.o_K D tilde.equiv M_s (E)
    $
    for some skewfield $E$, then
    $
      hat(A) tilde.equiv M_r (hat(D)) tilde.equiv M_(r s) (E).
    $
    This $E$ is the same as that which occurs in
    @th:local-hereditary-principal[(iv)], and $t = r s$.
  + The statements and proofs of @cor:complete-local-maximal-endomorphisms and
    @th:left-right-orders-maximal carry over unchanged to the present case where
    $R$ need not be complete.
  + #source(189)If $Delta$ is a maximal order in a skewfield $D$ with center
    $K$, @th:local-completion-comparison shows that
    $
      Delta slash rad Delta tilde.equiv hat(Delta) slash rad hat(Delta).
    $
    Here, $hat(Delta)$ is a maximal $hat(R)$-order in the central simple
    $hat(K)$-algebra $hat(D)$. But if $hat(D)$ is not a skewfield, then
    $hat(Delta) slash rad hat(Delta)$ is certainly _not_ a skewfield. Indeed, in
    terms of the notation of the first remark above, we have
    $
      hat(Delta) slash rad hat(Delta) tilde.equiv M_s (Omega slash rad Omega),
    $
    where $Omega$ is the maximal $hat(R)$-order in $E$.
] <rem:local-capacity>

Generalizing @th:complete-local-maximal-right-ideals, we have

#theorem[
  Let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$.
  + There is a one-to-one correspondence $J -> overline(J)$ between the set of
    maximal right ideals $J$ of $Lambda$, and the set of maximal right ideals
    $overline(J)$ of $Lambda slash rad Lambda$.
  + All maximal right ideals of $Lambda$ are mutually conjugate under inner
    automorphisms by units of $Lambda$.
  + If $x Lambda$ is a maximal right ideal of $Lambda$, then $Lambda x$ is a
    maximal left ideal of $Lambda$.
] <th:local-maximal-right-ideals>

#proof[
  The proof of (i) is exactly the same as in
  @th:complete-local-maximal-right-ideals. Next, let $x Lambda$ and $y Lambda$
  be maximal right ideals of $Lambda$. Since $Lambda slash x Lambda$ is an
  $R$-torsion module, it follows from Exercise~@exc:completion-residue-modules
  that there is a right $Lambda$-isomorphism
  $Lambda slash x Lambda tilde.equiv hat(Lambda) slash x hat(Lambda)$, whence
  $x hat(Lambda)$ is a maximal right ideal in $hat(Lambda)$. But then
  $hat(Lambda) x$ is a maximal left ideal in $hat(Lambda)$ by
  @th:complete-local-maximal-right-ideals, and so $Lambda x$ is a maximal left
  ideal in $Lambda$. This proves (iii).

  Next, by @th:complete-local-maximal-right-ideals there exists
  $u in u(hat(Lambda))$ such that $y hat(Lambda) = u dot x hat(Lambda)$. Choose
  $v in Lambda$ with $v equiv u (mod pi hat(Lambda))$; since $v, u$ have the
  same image in $Lambda slash pi Lambda$, and since
  $pi Lambda subset rad Lambda$, it follows from
  Exercise~@exc:units-modulo-radical that $v in u(Lambda)$. But then $y Lambda$
  and $v x Lambda$ are a pair of maximal right ideals of $Lambda$, having the
  same image in $Lambda slash rad Lambda$. It follows from (i) that
  $y Lambda = v x Lambda = v dot x Lambda dot v^(-1)$ as desired, which
  completes the proof.
]

#theorem[
  Let $Lambda$ be a maximal $R$-order in a separable $K$-algebra $A$. Then every
  one-sided ideal of $Lambda$ is principal. If $M$ and $N$ are left
  $Lambda$-lattices, then $M tilde.equiv N$ if and only if $K M tilde.equiv K N$
  as left $A$-modules.
] <th:separable-maximal-principal>

#proof[
  If $M tilde.equiv N$, then clearly $K M tilde.equiv K N$. Conversely if
  $K M tilde.equiv K N$ then $hat(K) hat(M) tilde.equiv hat(K) hat(N)$ as left
  $hat(A)$-modules. If we decompose $hat(A)$ into simple components, then there
  are corresponding decompositions
  $
    hat(Lambda) = dsum Lambda_i, quad hat(M) = dsum Lambda_i hat(M),
  $
  and each $Lambda_i$ is a maximal $R_i$-order in a central simple algebra, as
  in the proof of @th:local-maximal-hereditary. From the isomorphism
  $hat(K) hat(M) tilde.equiv hat(K) hat(N)$ it follows that
  $hat(K) dot Lambda_i hat(M) tilde.equiv hat(K) dot Lambda_i hat(N)$
  #source(190)for each $i$, whence by @th:local-hereditary-principal[(i)] we may
  conclude that $Lambda_i hat(M) tilde.equiv Lambda_i hat(N)$ for each $i$.
  Hence $hat(M) tilde.equiv hat(N)$, and so $M tilde.equiv N$ by
  @th:local-completion-comparison[(iii)].

  Finally, if $M$ is a left ideal of $Lambda$, then $K M = A e = K dot Lambda e$
  for some idempotent $e$ in the semisimple ring $A$. Thus
  $M tilde.equiv Lambda e$ by the first part of this proof, and the theorem is
  established.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

Unless otherwise stated, $R$ denotes a discrete valuation ring, not necessarily
complete.

#exercise[
  Let $Delta$ be a maximal $R$-order in a skewfield $D$ with center $K$. Show
  that every left $Delta$-lattice is free.
  #hint[@exc:skewfield-order-lattices-free][Since $Delta$ is hereditary, each
    left $Delta$-lattice $M$ is isomorphic to a direct sum of ideals of $Delta$.
    Each such ideal is principal, hence is isomorphic to $Delta$.]
  <hint:skewfield-order-lattices-free>
] <exc:skewfield-order-lattices-free>

#exercise[
  Prove @th:local-maximal-right-ideals[(ii), (iii)] without using the results
  for the case where $R$ is complete.
  #hint[@exc:local-maximal-ideals-direct][Let
    $overline(Lambda) = Lambda slash rad Lambda$, and let $x Lambda$, $y Lambda$
    be maximal right ideals of $Lambda$. Then $overline(x) overline(Lambda)$,
    $overline(y) overline(Lambda)$ are maximal right ideals of the simple ring
    $overline(Lambda)$. By Exercise~@exc:maximal-ideals-conjugate, there exists
    $u in u(overline(Lambda))$ such that
    $u dot overline(x) overline(Lambda) dot u^(-1)
    = overline(y) overline(Lambda)$. Choose $v in Lambda$ with
    $overline(v) = u$; then $v in u(Lambda)$ by
    Exercise~@exc:units-modulo-radical. Therefore
    $v dot x Lambda dot v^(-1) = y Lambda$, since these maximal right ideals
    have the same image in $overline(Lambda)$.

    Further, $overline(Lambda) overline(x)$ is a maximal left ideal of
    $overline(Lambda)$, by Exercise~@exc:maximal-ideals-conjugate. Therefore
    $Lambda x$ is a maximal left ideal of $Lambda$.]
  <hint:local-maximal-ideals-direct>
] <exc:local-maximal-ideals-direct>

#exercise[
  In this exercise, $R$ denotes a _semilocal_ Dedekind domain, that is, a
  Dedekind domain with only a finite number of maximal ideals
  ${P_1, dots, P_n}$. Let $Lambda$ be an $R$-order in a separable $K$-algebra
  $A$, and let $M, N$ be left $Lambda$-lattices. Show that $M tilde.equiv N$ if
  and only if $M_(P_i) tilde.equiv N_(P_i)$, $1 <= i <= n$.
  #hint[@exc:semilocal-isomorphism][Let $f_i : M_(P_i) tilde.equiv N_(P_i)$,
    $1 <= i <= n$. Replacing $f_i$ by $alpha f_i$, $alpha in R - P_i$, we may
    assume that each $f_i in Hom_Lambda (M, N)$. Choose
    $beta_1, dots, beta_n in R$ such that $beta_i equiv 1 (mod P_i)$,
    $beta_i equiv 0 (mod P_j)$, $j != i$. Set $f = sum beta_i f_i$, and show
    that $f : M -> N$ is an epimorphism, by verifying that
    $f_(P_i) : M_(P_i) -> N_(P_i)$ is epic for $1 <= i <= n$. Deduce from this
    that $f$ is an isomorphism.]
  <hint:semilocal-isomorphism>
] <exc:semilocal-isomorphism>

#exercise[
  Which of the results of this section remain true when $R$ is assumed to be a
  semilocal Dedekind domain, rather than a discrete valuation ring?
] <exc:semilocal-results>
