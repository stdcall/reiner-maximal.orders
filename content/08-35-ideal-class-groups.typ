#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/08-35-ideal-class-groups.typ": hom-inclusions

== Ideal class groups <sec:ideal-class-groups>

Throughout this section, let $R$ be a Dedekind domain with quotient field $K$,
and let $Lambda$ be a maximal $R$-order in a central simple $K$-algebra $A$. We
shall eventually restrict our attention to the case where $K$ is a global field,
so as to have available Eichler's Theorem and its consequences, but for the
moment $K$ may be arbitrary. We shall define the _ideal class group_#idx(
  "class group",
)#idx("ideal", "class group") of $Lambda$ denoted by $Cl Lambda$, and shall show
how to calculate it. The definition will be such that in the special case where
$Lambda = R$, $Cl Lambda$ will coincide with the ideal class group $Cl R$
defined in §~@sec:dedekind-domains.

#source(316)By a _left $Lambda$-ideal_ in $A$ we mean, as usual, a left
$Lambda$-lattice $M$ in $A$ such that $K M = A$. As in §~@sec:ideal-classes, two
left $Lambda$-ideals $M, N$ in $A$ are placed in the same _ideal class_#idx(
  "ideal",
  "class",
) if $M tilde.equiv N$ as left $Lambda$-modules, or equivalently, if $M = N x$
for some $x in u(A)$. Let us attempt to define a group structure on this set of
ideal classes. Given any two left $Lambda$-ideals $M$, $N$ in $A$, their product
$M dot N$ is also a left $Lambda$-ideal in $A$. However, when $A$ is
non-commutative, the ideal class of $M dot N$ is not necessarily determined by
the ideal classes of $M$ and $N$. Specifically, for each $x in u(A)$, the ideal
$M x$ is in the same class as $M$, but possibly $M x dot N$ and $M dot N$ are in
different classes.

Steinitz's Theorem @th:steinitz suggests one way of overcoming this difficulty.
The theorem states (as a special case) that given any two left $R$-ideals $J$,
$J'$ in $K$, then
$
  J dotplus J' tilde.equiv R dotplus J J' quad "as" R"-modules,"
$ <eq:steinitz-sum>
and furthermore,
$
  R dotplus J tilde.equiv R dotplus J' <=> "class of" J = "class of" J'
  <=> J tilde.equiv J'.
$ <eq:steinitz-cancellation>
These results show that the ideal class of the product $J J'$ can be computed
unambiguously from the structure of $J$ and $J'$ as $R$-modules.

In @th:left-ideals-genus we obtained a partial generalization of Steinitz's
Theorem. A special case of @th:left-ideals-genus asserts that given any pair of
left $Lambda$-ideals $M$, $M'$ in $A$, there exists a left $Lambda$-ideal $M''$
in $A$ such that
$
  M dotplus M' tilde.equiv Lambda dotplus M'' quad "as" Lambda"-modules."
$ <eq:ideal-sum-decomposition>
The isomorphism types of $M$ and $M'$ uniquely determine the isomorphism type of
the direct sum $M dotplus M'$, and hence that of $Lambda dotplus M''$. This
suggests a way of defining a binary operation on ideal classes. It is customary
to write this operation additively, so we tentatively define
$
  "ideal class of" M + "ideal class of" M' = "ideal class of" M''
$
whenever @eq:ideal-sum-decomposition holds true. In order to prove that the
operation is well defined, we would need to establish a "cancellation theorem"
analogous to @eq:steinitz-cancellation. Specifically, we would need to prove
that if $M$, $N$ are any left $Lambda$-ideals in $A$, then
$
  Lambda dotplus M tilde.equiv Lambda dotplus N ==> M tilde.equiv N.
$ <eq:ideal-cancellation>
Unfortunately, there are examples in which @eq:ideal-cancellation is false (see
Swan [@bib:Swan1962]).

The fact that @eq:ideal-cancellation is not always true forces us to introduce a
new equivalence relation on the set of $Lambda$-ideals, weaker than isomorphism.
It is convenient to define this relation not only for $Lambda$-ideals, but more
generally for $Lambda$-modules. Given any two left $Lambda$-modules $X$, $Y$, we
call $X$ _stably isomorphic_ #idx("stable isomorphism")#source(317)to $Y$ if
there exists a non-negative integer $r$ such that
$
  X dotplus Lambda^((r)) tilde.equiv Y dotplus Lambda^((r)) quad "as left"
  Lambda"-modules."
$
It is easily verified that stable isomorphism is an equivalence relation on the
set of all left $Lambda$-modules. Clearly, isomorphism implies stable
isomorphism, but not conversely (in general). Let $[X]$ denote the stable
isomorphism class of the $Lambda$-module $X$.

#theorem[
  Let $Cl Lambda$ denote the set of stable isomorphism classes of left
  $Lambda$-ideals in $A$. Define an additive structure on $Cl Lambda$ as
  follows: given any pair of left $Lambda$-ideals $M, M'$ in $A$, we set
  $
    [M] + [M'] = [M''],
  $
  where $M''$ is any left $Lambda$-ideal in $A$ such that
  $
    M dotplus M' tilde.equiv Lambda dotplus M''.
  $
  Then $Cl Lambda$ is an abelian additive group, with identity element
  $[Lambda]$. #idx("class group", target: [@th:stable-class-group])#idx(
    "ideal",
    "class group",
    target: [@th:stable-class-group],
  )
] <th:stable-class-group>

#proof[
  Given $M$ and $M'$, the existence of an ideal $M''$ such that
  @eq:ideal-sum-decomposition holds, is guaranteed by @th:left-ideals-genus. It
  is worth pointing out that if $M''$ is a left $Lambda$-_module_ satisfying
  @eq:ideal-sum-decomposition, then in fact $M''$ is isomorphic to a left
  $Lambda$-ideal in $A$ (see Exercise~@exc:summand-in-free-lattice).

  Let us show that addition of stable isomorphism classes is well defined. Let
  $N, N'$ be left $Lambda$-ideals in $A$ such that
  $
    [M] = [N], quad [M'] = [N'], quad
    N dotplus N' tilde.equiv Lambda dotplus N''.
  $
  Then there exists an $s >= 0$ such that
  $
    M dotplus Lambda^((s)) tilde.equiv N dotplus Lambda^((s)), quad
    M' dotplus Lambda^((s)) tilde.equiv N' dotplus Lambda^((s)).
  $
  But then $[M''] = [N'']$, since
  $
    M'' dotplus Lambda^((2s+1)) tilde.equiv M dotplus M' dotplus Lambda^((2s))
    tilde.equiv N dotplus N' dotplus Lambda^((2s))
    tilde.equiv N'' dotplus Lambda^((2s+1)).
  $
  Thus addition is well defined. It is easily verified that addition is
  associative and commutative, and that
  $
    [Lambda] + [M] = [M] quad "for all" quad [M] in Cl Lambda.
  $

  It remains to prove the existence of inverses. Any left $Lambda$-ideal $M$ in
  $A$ is $Lambda$-projective, by @cor:global-lattices-projective. Hence there
  exists a left $Lambda$-lattice $Y$ such that
  $
    M dotplus Y tilde.equiv Lambda^((t)) quad "for some" t.
  $
  By Exercise~@exc:summand-in-free-lattice, $Y$ is isomorphic to a submodule of
  $Lambda^((t-1))$. Therefore by @th:lattice-free-plus-ideal there exists a left
  $Lambda$-ideal $N$ in $A$ such that
  #source(318)
  $
    Y tilde.equiv N dotplus Lambda^((t-2)),
  $
  so we now have
  $
    M dotplus N dotplus Lambda^((t-2)) tilde.equiv Lambda^((t)).
  $
  Let $M dotplus N tilde.equiv Lambda dotplus L$ for some left $Lambda$-ideal
  $L$ in $A$; then $[M] + [N] = [L]$, by the definition of addition of stable
  isomorphism classes. However,
  $
    L dotplus Lambda^((t-1)) tilde.equiv L dotplus Lambda dotplus Lambda^((t-2))
    tilde.equiv M dotplus N dotplus Lambda^((t-2)) tilde.equiv Lambda^((t)),
  $
  so $[L] = [Lambda]$. Thus $[M] + [N] = 0$ in $Cl Lambda$, and so inverses
  exist. This completes the proof that $Cl Lambda$ is a group.
]

It follows at once from @eq:steinitz-sum and @eq:steinitz-cancellation that when
$Lambda = R$, the group $Cl Lambda$ coincides with the class group $Cl R$
defined in §~@sec:dedekind-domains. It should also be remarked that when $K$ is
a global field and $Lambda$ is any maximal $R$-order, then the ideal class group
$Cl Lambda$ is necessarily a finite group, by the Jordan–Zassenhaus Theorem
@th:jordan-zassenhaus.

For the remainder of this section, we shall restrict our attention to the case
where $K$ is a global field. Let us introduce the _ray class group_ $Cl_A R$;
#idx("ray class group")this is a modified version of $Cl R$, with the
modification depending on the given central simple $K$-algebra $A$. We shall use
the following notation: #idx("ray group")
$
     I(R) & = "multiplicative group of" R"-ideals in" K, \
     P(R) & = "subgroup of principal ideals" = {R alpha : alpha in K^*}, \
     Cl R & = I(R) slash P(R) = "ideal class group of" R, \
        S & = "set of all infinite primes of" K "ramified in" A, \
     U(A) & = {alpha in K^* : alpha_P > 0 "for each" P in S}, \
  P_A (R) & = {R alpha : alpha in U(A)} = "ray group" (mod S), \
   Cl_A R & = I(R) slash P_A (R) = italic("ray class group") (mod S).
$

The groups $P_A (R)$ and $P(R)$ may coincide, even when $S$ is non-empty; this
certainly occurs when $R = bold(Z)$, for example. In general, $P_A (R)$ is a
subgroup of $P(R)$, and there is an epimorphism $sigma : Cl_A R -> Cl R$. By
Exercise~@exc:ray-class-kernel, $ker sigma$ is a finite elementary abelian
2-group.

The main result of this section is the fact that the reduced norm map on
$Lambda$-ideals induces an isomorphism $Cl Lambda tilde.equiv Cl_A R$ if $K$ is
an algebraic number field. This isomorphism also holds for the function field
case, if we assume that $A$ satisfies the Eichler condition relative to $R$.
Eichler's Theorem @th:eichler plays a key role in the proof of these results. We
may restate @cor:eichler-ideal-classes[Corollary] of Eichler's Theorem in our
present notation, as follows:

#theorem[
  Let $K$ be a global field, and let $Gamma$ be a maximal $R$-order in a central
  simple $K$-algebra $B$, where $B = eichler(R)$. For each left $Gamma$-ideal
  $L$ in $B$, let $nu(L)$ denote the class of the $R$-ideal $nr_(B slash K) L$
  in the ray class group $Cl_B R$. #source(319)Then for each pair of left
  $Gamma$-ideals $L, L'$ in $B$, we have
  $
    L tilde.equiv L' quad "as" Gamma"-modules" <==> nu(L) = nu(L').
  $
] <th:eichler-ray-classes>

A preliminary calculation is necessary before we can apply this result. Given
the central simple $K$-algebra $A$, we set $B = M_r (A)$, where $r >= 1$. Then
$B$ is also central simple over $K$, and a prime of $K$ ramifies in $B$ if and
only if it ramifies in $A$. Hence $P_A (R) = P_B (R)$, and the ray class group
$Cl_B R$ coincides with $Cl_A R$. Let $Gamma = M_r (Lambda)$, so by
@th:matrix-maximal-order $Gamma$ is a maximal $R$-order in $B$. Each left
$Gamma$-ideal $L$ in $B$ determines an element $nu(L) in Cl_A R$, where
$
  nu(L) = "image of" quad nr_(B slash K) L quad "in" Cl_A R.
$ <eq:ray-class-of-norm>
Let us recall from §~@sec:norms-of-ideals that by definition,
$
  nr_(B slash K) L = {N_(B slash K) L}^(1 slash s), quad "where" quad
  (B : K) = s^2.
$
Further, if $L subset Gamma$ then
$
  N_(B slash K) L = ord_R Gamma slash L.
$
We are now ready to prove

#lemma[
  Let $r >= 1$, and let
  $
    B = Hom_A (A^((r)), A^((r))) tilde.equiv M_r (A),
  $
  where $A^((r))$ is viewed as a left $A$-, right $B$-bimodule. Let
  $
    Gamma = Hom_Lambda (Lambda^((r)), Lambda^((r))) tilde.equiv M_r (Lambda).
  $
  To each left $Lambda$-lattice $X$ in $A^((r))$ there corresponds a left
  $Gamma$-lattice $phi(X)$ in $B$, given by
  $phi(X) = Hom_Lambda (Lambda^((r)), X)$. If
  $X = J_1 dotplus dots.c dotplus J_r$, where each $J_i$ is a left
  $Lambda$-ideal in $A$, then
  $
    nr_(B slash K) phi(X) = product_(i=1)^r nr_(A slash K) J_i.
  $ <eq:norm-of-hom-lattice>
  Therefore
  $
    nu{phi(X)} = product_(i=1)^r nu(J_i) quad "in" Cl_A R,
  $ <eq:ray-class-of-hom-lattice>
  where $nu(J_i)$ denotes the class of $nr_(A slash K) J_i$ in $Cl_A R$.
] <lem:matrix-order-norms>

#proof[
  The left $Lambda$-module $Lambda^((r))$ is a progenerator for the category
  $lmodule(Lambda, cal(M))$. Hence by @cor:progenerator-equivalence or
  @th:morita-equivalence, there is an equivalence of categories
  $
    phi : lmodule(Lambda, cal(M)) -> lmodule(Gamma, cal(M)), quad "where" quad
    phi = Hom_Lambda (Lambda^((r)), dot).
  $
  Then $phi$ maps $Lambda^((r))$ onto $Gamma$, and carries each
  $Lambda$-submodule $X$ of $Lambda^((r))$ onto a #source(320)left ideal
  $phi(X)$ in $Gamma$. By tensoring with the field $K$, we find readily that
  $phi$ carries each $Lambda$-lattice $X$ in $A^((r))$ onto a $Gamma$-lattice
  $phi(X)$ in $B$. The correspondence $X -> phi(X)$ is one-to-one, and preserves
  isomorphism.

  Now let $X$ be any $Lambda$-lattice in $A^((r))$ such that $K X = A^((r))$. By
  @th:lattice-free-plus-ideal we may write $X = J_1 dotplus dots.c dotplus J_r$,
  where each $J_i$ is a left $Lambda$-ideal in $A$. Since the reduced norm is
  multiplicative, it suffices to prove formulas @eq:norm-of-hom-lattice and
  @eq:ray-class-of-hom-lattice for the case where $X subset Lambda^((r))$, and
  each $J_i subset Lambda$. We have a commutative diagram
  $
    #hom-inclusions
  $
  where the vertical arrows are inclusions, and the indicated isomorphisms are
  $R$-isomorphisms. Therefore
  $
    N_(B slash K) phi(X) = ord_R phi(Lambda^((r))) slash phi(X)
    = {ord_R Lambda^((r)) slash X}^r.
  $
  But
  $
    ord_R Lambda^((r)) slash X = product_(i=1)^r ord_R Lambda slash J_i
    = product_(i=1)^r N_(A slash K) J_i.
  $
  If $(A : K) = n^2$, then $(B : K) = r^2 n^2$, and so
  $
    N_(A slash K) = {nr_(A slash K)}^n, quad
    N_(B slash K) = {nr_(B slash K)}^(r n).
  $
  Hence we obtain
  $
    {nr_(B slash K) phi(X)}^(r n)
    = {product_(i=1)^r {nr_(A slash K) J_i}^n}^r,
  $
  which gives @eq:norm-of-hom-lattice at once. Formula
  @eq:ray-class-of-hom-lattice follows from @eq:norm-of-hom-lattice by taking
  images in $Cl_A R$, and the proof is complete.
]

#corollary[
  Let $K$ be a global field, and keep the above notation. Let $r >= 1$, and let
  $
    X = dsum_(i=1)^r J_i, quad X' = dsum_(i=1)^r J'_i,
  $
  where each $J_i$ and $J'_i$ is a left $Lambda$-ideal in $A$. Then
  + $X tilde.equiv X'$ as $Lambda$-modules if and only if
    $phi(X) tilde.equiv phi(X')$ as $Gamma$-modules.
  + If $X tilde.equiv X'$, then $nu phi(X) = nu phi(X')$, that is,
    $
      product_(i=1)^r nu(J_i) = product_(i=1)^r nu(J'_i).
    $ <eq:ray-classes-of-sums>
  + If $A = eichler(R)$, then $X tilde.equiv X'$ if and only if
    @eq:ray-classes-of-sums holds.
  + #source(321)Let $K$ be an algebraic number field and let $r >= 2$. Then
    $X tilde.equiv X'$ if and only if @eq:ray-classes-of-sums holds true, even
    when $A != eichler(R)$.
] <cor:sums-of-ideals-isomorphic>

#proof[
  Assertion (i) has already been established at the beginning of the proof of
  @lem:matrix-order-norms. From @lem:matrix-order-norms we also know that
  $
    nu phi(X) = product_(i=1)^r nu(J_i), quad
    nu phi(X') = product_(i=1)^r nu(J'_i).
  $
  If $X tilde.equiv X'$, then $phi(X) = phi(X') dot b$ for some $b in u(B)$.
  Therefore $nu phi(X) = nu phi(X')$ since $(nr_(B slash K) b) R in P_B (R)$,
  and (ii) is proved.

  Suppose for the moment that $A = eichler(R)$; then also $B = eichler(R)$.
  Hence by @th:eichler-ray-classes we know that $phi(X) tilde.equiv phi(X')$ if
  and only if $nu phi(X) = nu phi(X')$, and this establishes (iii).

  Finally, suppose that $K$ is an algebraic number field and $r >= 2$. Then
  $B = eichler(R)$, _whether or not_ $A = eichler(R)$. Indeed, if
  $A != eichler(R)$, then $(A : K) = 4$; but then $(B : K) = 4r^2 > 4$, so
  necessarily $B = eichler(R)$. But once we know that $B = eichler(R)$, we may
  use @th:eichler-ray-classes to deduce that $phi(X) tilde.equiv phi(X')$ if and
  only if $nu phi(X) = nu phi(X')$. This gives assertion (iv) and completes the
  proof of the corollary.
]

Let us record an important special case of @cor:sums-of-ideals-isomorphic.

#corollary[
  Keep the above notation, and let $J$, $J'$ be left $Lambda$-ideals in $A$. Let
  $[J]$ denote the stable isomorphism class of $J$.
  + If $A = eichler(R)$, then $[J] = [J']$ if and only if $J tilde.equiv J'$.
  + Let $K$ be an algebraic number field. Whether or not $A = eichler(R)$, we
    have
    $
      [J] = [J'] <==> J dotplus Lambda tilde.equiv J' dotplus Lambda.
    $
] <cor:stable-isomorphism-ideals>

#proof[
  By definition of stable isomorphism, $[J] = [J']$ if and only if
  $J dotplus Lambda^((r)) tilde.equiv J' dotplus Lambda^((r))$ for some
  $r >= 0$. By @eq:ray-class-of-hom-lattice,
  $
    nu phi(J dotplus Lambda^((r))) = nu(J).
  $
  Hence if $[J] = [J']$, then $nu(J) = nu(J')$. Therefore $J tilde.equiv J'$ by
  @cor:sums-of-ideals-isomorphic[(iii)], if $A = eichler(R)$. This proves
  assertion (i).

  Now let $K$ be an algebraic number field. From $nu(J) = nu(J')$ it follows
  that
  $
    nu phi(J dotplus Lambda) = nu phi(J' dotplus Lambda).
  $
  Therefore $J dotplus Lambda tilde.equiv J' dotplus Lambda$ by
  @cor:sums-of-ideals-isomorphic[(iv)], which completes the proof of the
  corollary.
]

We are now ready to prove

#theorem(major: true, title: [Swan [@bib:Swan1962]])[
  #source(322)Keep the above notation. If $K$ is an algebraic number field, or
  if $K$ is a function field and $A = eichler(R)$, then the reduced norm map
  induces an isomorphism
  $
    nu : Cl Lambda tilde.equiv Cl_A R.
  $
  Here, $Cl Lambda$ is the additive group of stable isomorphism classes of left
  $Lambda$-ideals in $A$, and $Cl_A R$ the multiplicative ray class group (mod
  $S$), where $S$ is the set of all infinite primes of $K$ which ramify in $A$.
] <th:swan-class-group>

#proof[
  Let $J, J'$ denote left $Lambda$-ideals in $A$. We shall define the map $nu$
  on $Cl Lambda$ by setting
  $
    nu[J] = nu(J) = "image of" quad nr_(A slash K) J quad "in" Cl_A R.
  $
  It follows from the proof of @cor:stable-isomorphism-ideals that $nu$ is well
  defined on $Cl Lambda$, since we showed there that if $[J] = [J']$, then
  $nu(J) = nu(J')$.

  Now let $J dotplus J' tilde.equiv Lambda dotplus J''$ for some $Lambda$-ideal
  $J''$. Then $nu(J) nu(J') = nu(J'')$ by @cor:sums-of-ideals-isomorphic[(ii)].
  Therefore
  $
    nu{[J] + [J']} = nu[J''] = nu[J] nu[J'],
  $
  so $nu$ is a homomorphism. If $nu[J] = 1$, then $nu(J) = nu(Lambda)$. By
  virtue of the hypotheses of this theorem, we may apply
  @cor:stable-isomorphism-ideals to conclude that
  $J dotplus Lambda tilde.equiv Lambda dotplus Lambda$. Therefore
  $[J] = [Lambda] = 0$ in $Cl Lambda$, and thus $nu$ is monic.

  Finally, the group $I(R)$ is the free abelian group generated by the nonzero
  prime ideals $P$ of $R$. Given $P$, we may find a maximal integral ideal $J$
  of $Lambda$ such that $P Lambda subset J subset Lambda$. Then
  $nr_(A slash K) J = P$ by @th:reduced-norm-maximal-ideal, and so $nu[J]$
  equals the image of $P$ in $Cl_A R$. This shows that $nu$ is epic, and
  completes the proof of the theorem.
]

#remark(kind: "Remarks", numbered: false)[
  + If $A = eichler(R)$, then there is a one-to-one correspondence between
    $Cl_A R$ and the set of isomorphism classes of left $Lambda$-ideals in $A$.
  + Some of the preceding theorems extend to non-maximal orders. We refer the
    reader to Fröhlich [@bib:Frohlich1973], Jacobinski [@bib:Jacobinski1966,
    @bib:Jacobinski1968a], Roggenkamp [@bib:Roggenkamp1970a], Swan–Evans
    [@bib:Swan1970], Wilson [@bib:Wilson1977]. Fröhlich's article contains a
    different proof of @th:swan-class-group, based on an idele-theoretic version
    of Eichler's Theorem.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $L$, $M$ be left $Lambda$-lattices such that $K L tilde.equiv A^((r))$,
  $K M tilde.equiv A^((s))$, and let $X$ be any left $Lambda$-module such that
  $
    L dotplus M tilde.equiv Lambda dotplus X.
  $
  Show that $X$ is isomorphic to a left $Lambda$-submodule of
  $Lambda^((r+s-1))$. #hint[@exc:summand-in-free-lattice][Since $X$ is
    isomorphic to a submodule of the $Lambda$-lattice $L dotplus M$, it follows
    that $X$ is also a $Lambda$-lattice. Tensor the given isomorphism with $K$,
    to obtain
    #source(323)
    $
      A^((r)) dotplus A^((s)) tilde.equiv A dotplus K X.
    $
    Hence $K X tilde.equiv A^((r+s-1))$ by Exercise~@exc:cancellation. Replacing
    $X$ by an isomorphic copy, we may assume that
    $K X = A^((r+s-1)) = K dot Lambda^((r+s-1))$. We may then choose a nonzero
    $alpha in R$ such that $alpha X subset Lambda^((r+s-1))$, and surely
    $X tilde.equiv alpha X$.] <hint:summand-in-free-lattice>
] <exc:summand-in-free-lattice>

#exercise[
  Show that the kernel of the epimorphism $Cl_A R -> Cl R$ is a finite
  elementary abelian 2-group. #hint[@exc:ray-class-kernel][The kernel is
    isomorphic to $P(R) slash P_A (R)$, which is in turn a homomorphic image of
    $K^* slash U(A)$. But there is an exact sequence
    $
      1 -> U(A) -> K^* stretch(->)^theta product_(P in S) {plus.minus 1} -> 1,
    $
    where for $a in K^*$ and $P in S$, the $P$-th component of $theta(a)$ is the
    sign of $a_P$ in $K_P$.] <hint:ray-class-kernel>
] <exc:ray-class-kernel>
