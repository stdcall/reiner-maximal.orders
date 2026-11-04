#import "main-defs.typ": *
#import "statements.typ": *

== Definitions and examples <sec:orders-definitions-and-examples>

For any finite dimensional $K$-space $V$, a _full $R$-lattice_ in $V$ is a
finitely generated $R$-submodule $M$ in $V$ such that $K dot M = V$, where #idx(
  "full lattice",
)#idx("lattice")
$
  K dot M = {sum alpha_i m_i "(finite sum)" : alpha_i in K, m_i in M}.
$
An _$R$-order_ in the $K$-algebra $A$ is a subring $Lambda$ of $A$, having the
same unity element as $A$, and such that $Lambda$ is a full $R$-lattice in $A$.
Note that $Lambda$ is both left and right noetherian, since $Lambda$ is finitely
generated over the noetherian domain $R$.
#idx("order")

Let us give some examples of orders:
+ If $A = M_n (K)$, the algebra of all $n times n$ matrices over $K$, then
  $Lambda = M_n (R)$ is an $R$-order in $A$.
+ Let $R$ be a Dedekind domain, and let $L$ be a finite separable extension of
  $K$. Denote by $S$ the integral closure of $R$ in $L$. Then $S$ is an
  $R$-order in $L$ (see @th:integral-closure-finitely-generated). In particular,
  taking $R = bold(Z)$, we see that $algint {L}$ is a $bold(Z)$-order in $L$.
+ Let $a in A$ be integral over $R$, that is, $a$ is a zero of a monic
  polynomial over $R$. Then the ring $R[a]$ is an $R$-order in the $K$-algebra
  $K[a]$.
+ Let $G$ be a finite group, and let $A = K G$ be its _group algebra_ over $K$,
  that is, $K G$ consists of all formal sums $sum_(x in G) alpha_x dot x$,
  $alpha_x in K$, with
  #idx("group algebra")
  $
    (sum alpha_x dot x) + (sum beta_x dot x) = sum (alpha_x + beta_x) dot x, \
    (sum alpha_x dot x)(sum beta_y dot y) = sum_(x, y) alpha_x beta_y dot (x y).
  $
  #source(118)Then $R G = {sum_(x in G) alpha_x x : alpha_x in R}$ is an
  $R$-order in $A$.

From example (ii) it is evident that the study of orders includes as a special
case the classical subject of algebraic number theory. On the other hand, in
dealing with representations of a finite group $G$ by means of matrices with
entries in a domain $R$, one of the first steps is to pass from matrix theory to
the study of $R G$-modules (see Curtis–Reiner [@bib:Curtis1962]), so as to be
able to take advantage of the ring structure of $R G$. Thus the study of orders
also includes the theory of integral representations of finite groups.

Let us show at once that every $K$-algebra $A$ contains $R$-orders. Let $M$ be
any full $R$-lattice in $A$; such $M$'s exist, and indeed if $A = dsum K x_i$,
then $dsum R x_i$ is a full $R$-lattice in $A$. We define the _left order_ of
$M$ as #idx("left order")#idx("order", "left")
$
  O_l (M) = {x in A : x M subset M}.
$ <eq:left-order>
Clearly $O_l (M)$ is a subring of $A$, and is an $R$-module. Let us verify that
$O_l (M)$ is a full $R$-lattice in $A$. For each $y in A$, $y M$ is an
$R$-lattice in $A$, and so by §~@sec:dedekind-domains there exists a nonzero
$r in R$ such that $r dot y M subset M$. Thus $r y in O_l (M)$, which proves
that $K dot O_l (M) = A$. Next, there exists a nonzero $s in R$ such that
$s dot 1_R in M$. Therefore $O_l (M) dot (s dot 1_R) subset M$, whence
$O_l (M) subset s^(-1) M$. Since $R$ is noetherian and $s^(-1) M$ is an
$R$-lattice, the above implies that $O_l (M)$ is also an $R$-lattice. This
completes the proof that $O_l (M)$ is an $R$-order in $A$. Likewise, the _right
order_ #idx("right order")#idx("order", "right")
$
  O_r (M) = {x in A : M x subset M}
$ <eq:right-order>
is an $R$-order in $A$.

For a full $R$-lattice $M$ in $A$, and an $R$-order $Gamma$ in $A$ such that
$Gamma dot M subset M$, let us compute $Hom_Gamma (M, M)$. Each
$phi in Hom_Gamma (M, M)$ extends uniquely to an element of $Hom_A (K M, K M)$,
hence is given by a right multiplication by an element of $O_r (M)$. Thus we
have an identification
$
  O_r (M) = Hom_Gamma (M, M),
$ <eq:right-order-endomorphisms>
where $M$ is a left $Gamma$-module. _Note that $Hom_Gamma (M, M)$ does not
depend on the choice of the $R$-order $Gamma$ in $A$._

Now let $R'$ be an integral domain containing $R$, with quotient field $K'$.
Then $R' times.o_R M$ is a full $R'$-lattice in the $K'$-algebra
$K' times.o_K A$. Since $M$ is finitely generated over the noetherian ring
$Gamma$, we have by @th:change-of-rings-ext
$
  R' times.o_R Hom_Gamma (M, M) tilde.equiv
  Hom_(R' times.o_R Gamma) (R' times.o_R M, R' times.o_R M),
$
provided that $R'$ is $R$-flat. It then follows from
@eq:right-order-endomorphisms that there is a ring isomorphism
$
  R' times.o_R O_r (M) tilde.equiv O_r (R' times.o_R M).
$ <eq:right-order-base-change>
#source(119)This holds in particular if $R'$ is any ring of quotients of $R$.
Hence
$
  O_r (M_P) = {O_r (M)}_P
$ <eq:right-order-local>
for each prime ideal $P$ of $R$. Here, the subscript $P$ indicates localization
at $P$ (see §~@ss:localization-at-prime-ideals).

The following result is fundamental:

#theorem[
  Every element of an $R$-order $Lambda$ is integral over $R$. Furthermore, if
  $R$ is integrally closed, then for each $a in Lambda$ we have
  $
    minpol_K a in R[X], quad charpol_(A slash K) a in R[X].
  $
] <th:order-elements-integral>

#proof[
  For each $a in Lambda$, it follows from the inclusion $R[a] subset Lambda$
  that $R[a]$ is a finitely generated $R$-module, so $a$ is integral over $R$ by
  @th:integral-criteria. If we assume in addition that $R$ is integrally closed,
  the remaining assertions are consequences of
  @th:integral-over-integrally-closed and Exercise~@exc:char-pol-integral.
]

A _maximal_ $R$-order in $A$ is an $R$-order which is not properly contained in
any other $R$-order in $A$. If the integral closure $R^"cl"$ of $R$ in $A$
happens to be an $R$-order in $A$, then by @th:order-elements-integral $R^"cl"$
is automatically the unique maximal $R$-order in $A$. However, most of the time
$R^"cl"$ is not a ring; furthermore, even in the case where $A$ is commutative,
so that $R^"cl"$ is a ring by @cor:sum-product-integral, it may happen that
$R^"cl"$ is not an $R$-lattice. Thus, in example (ii) of maximal orders given
above, if we drop the hypothesis of separability of $L$ over $K$, then $S$ need
not be finitely generated as $R$-module (see Artin [@bib:Artin1950]); in this
case, there are no maximal $R$-orders in $L$. #idx("maximal order")#idx(
  "order",
  "maximal",
)

By way of reassurance, as well as for later use, we now prove

#theorem[
  If $Lambda$ is a maximal $R$-order in $A$, then for each $n$, $M_n (Lambda)$
  is a maximal $R$-order in $M_n (A)$. If $R$ is integrally closed, then
  $M_n (R)$ is a maximal $R$-order in $M_n (K)$.
] <th:matrix-maximal-order>

#proof[
  Let $B = M_n (A)$, $Gamma = M_n (Lambda)$, where $Lambda$ is a maximal
  $R$-order in $A$. Clearly $Gamma$ is an $R$-order in $B$. Let
  $Gamma subset Gamma'$, where $Gamma'$ is an $R$-order in $B$, and let
  $Lambda'$ be the set of all those elements of $A$ which occur as some entry of
  some matrix in $Gamma'$. Obviously $Lambda subset Lambda' subset A$, and we
  shall show that $Lambda'$ is an $R$-order in $A$. Let $lambda in Lambda'$
  occur in the $(r, s)$-position of a matrix $X in Gamma'$. We can find
  permutation matrices $P_1, P_2 in Gamma$ such that $lambda$ occurs in the
  $(1, 1)$-position of $P_1 X P_2 in Gamma'$. Let
  $E_lambda = diag(lambda, 0, dots, 0) in M_n (Lambda')$. Then
  $
    E_lambda = E_1 P_1 X P_2 E_1 in Gamma' quad "for all" lambda in Lambda'.
  $
  Since
  $
    E_lambda + E_mu = E_(lambda + mu), quad E_lambda E_mu = E_(lambda mu),
    quad r E_lambda = E_(r lambda), quad lambda, mu in Lambda', quad r in R,
  $
  #source(120)it follows that $Lambda'$ is a ring containing $R$. Further, the
  map $lambda -> E_lambda$, $lambda in Lambda'$, embeds $Lambda'$ in the
  $R$-lattice $Gamma'$, and hence $Lambda'$ is also an $R$-lattice.

  The above shows that $Lambda'$ is an $R$-order in $A$. Therefore
  $Lambda' = Lambda$, since $Lambda$ is maximal. Hence every entry of every
  matrix in $Gamma'$ lies in $Lambda$, whence $Gamma' subset Gamma$. This shows
  that $Gamma = Gamma'$, and proves that $Gamma$ is a maximal order. If $R$ is
  integrally closed, then $R$ is a maximal $R$-order in $K$, so the second
  assertion in the theorem is the special case of the first assertion, in which
  $A = K$, $Lambda = R$.
]

We shall see in
§§~@sec:maximal-orders-complete-local-case–@sec:maximal-orders-local-case that
under suitable hypotheses on $R$ and $A$, the converse of
@th:matrix-maximal-order is true: _every_ maximal $R$-order in $M_n (A)$ is of
the form $M_n (Lambda)$ for some maximal $R$-order $Lambda$ in $A$.

To conclude this section, let us consider the situation where an integral domain
$R$ is contained in a larger integral domain $R'$ having the same quotient field
as $R$. For convenience, we treat only the case where $R$ is a Dedekind domain.
We shall show that every $R'$-order $Lambda'$ comes from an $R$-order $Lambda$
by extension of the ground ring from $R$ to $R'$, and that likewise every
$Lambda'$-lattice comes from some $Lambda$-lattice.

#theorem[
  Let $R$ be a Dedekind ring with quotient field $K$, and let $R'$ be an
  integral domain such that $R subset R' subset K$. Then
  + Every $R'$-lattice $M'$ contains an $R$-lattice $M$ such that $M' = R' M$.
  + Every $R'$-order $Lambda'$ (in a finite dimensional $K$-algebra $A$)
    contains an $R$-order $Lambda$ in $A$, such that $Lambda' = R' Lambda$.
  + Let $Lambda' = R' Lambda$, as in (ii). Then every left $Lambda'$-lattice
    $M'$ contains a left $Lambda$-lattice $M$ such that $M' = Lambda' M = R' M$.
] <th:orders-over-larger-ring>

#proof[
  It is clear that $K$ is the quotient field of $R'$. The domain $R'$ is also a
  Dedekind domain (see references listed in §~@sec:dedekind-domains), though we
  shall not require this fact here. To prove (i), we note that any $R'$-lattice
  $M'$ can be written as a sum
  $
    M' = sum_(i=1)^s R' m_i, quad m_i in M'.
  $
  Set $M = sum R m_i$; then $M$ is an $R$-lattice in $M'$ such that $R' M = M'$,
  as desired.

  As usual, we identify an $R$-lattice $M$ with its image $1 times.o M$ in
  $K times.o_R M$, and denote the latter by $K M$. We may then compute the
  $R'$-module $R' M$ in $K M$. Let us show that
  $
    R' times.o_R M tilde.equiv R' M subset K M.
  $ <eq:extension-lattice>
  Indeed, the above $R'$-isomorphism holds when $M = R$, and hence by
  @rem:free-then-projective it also holds true for every projective $R$-module.
  Since $R$ is a Dedekind domain, by @th:steinitz every $R$-lattice is
  $R$-projective. This proves @eq:extension-lattice, and we may hereafter
  identify $R' times.o_R M$ with $R' M$, by means of the map
  $alpha times.o m -> alpha m$, $alpha in R'$, $m in M$.

  #source(121)In order to apply the "Change of Rings" Theorem
  @th:change-of-rings-ext, we shall need to know that $R'$ is $R$-flat. If $X$
  is any finitely generated $R$-submodule of $R'$, then $X$ is an $R$-lattice.
  Therefore $X$ is $R$-projective, and hence $X$ is $R$-flat by
  @cor:projective-flat. This shows that every finitely generated $R$-submodule
  of $R'$ is $R$-flat, whence also $R'$ is $R$-flat by
  @th:flat-finitely-generated-submodules.

  Now let $Lambda'$ be an $R'$-order in $A$. By (i), we may choose an
  $R$-lattice $L$ in $Lambda'$ such that $Lambda' = R' L$. We set
  $
    Lambda = O_r (L) = {x in A : L x subset L}, quad Gamma = O_l (L).
  $
  Then $Lambda$ and $Gamma$ are $R$-orders in $A$, and there is an
  identification $Lambda = Hom_Gamma (L, L)$, where $L$ is viewed as left
  $Gamma$-module. By @th:change-of-rings-ext we obtain
  $
    R' Lambda = R' times.o_R Lambda = Hom_(R' Gamma) (R' L, R' L)
    = Hom_(R' Gamma) (Lambda', Lambda') = O_r (Lambda') = Lambda'.
  $
  Therefore $R' Lambda = Lambda'$, and (ii) is proved.

  Finally, any left $Lambda'$-lattice $M'$ may be written as
  $
    M' = sum_(i=1)^s Lambda' m_i, quad m_i in M'.
  $
  Then $M = sum Lambda m_i$ is a left $Lambda$-lattice in $M'$ such that
  $M' = Lambda' M$. Furthermore, $R' M = R'(Lambda M) = Lambda' M$. This
  completes the proof of the theorem.
]

#heading(level: 3, numbering: none, outlined: false)[Exercise]

#exercise[
  Let $R$ be a noetherian integrally closed domain with quotient field $K$, and
  let $A$ be a finite dimensional $K$-algebra. Let $Gamma$ be a subring of $A$
  containing $R$, and suppose that $Gamma$ is a finitely generated $R$-module.
  Show that $Gamma$ is contained in an $R$-order in $A$.
  #hint[@exc:subring-in-order][if $M$ is any full $R$-lattice in $A$, then so is
    $M dot Gamma$, and $Gamma subset O_r (M dot Gamma)$.]
  <hint:subring-in-order>
] <exc:subring-in-order>
