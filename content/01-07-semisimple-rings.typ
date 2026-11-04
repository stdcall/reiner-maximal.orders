#import "main-defs.typ": *
#import "statements.typ": *

== Semisimple rings and simple algebras <sec:semisimple-rings>

=== Wedderburn's Theorem <ss:wedderburn-theorem>

#source(99)Recall that a ring $A$ is _semisimple_#idx("semisimple (ring)") if
$rad A = 0$. Of particular interest, because they occur so frequently in
practice, are the left artinian semisimple rings. The algebraic structure of
such rings can be described explicitly, as we shall see below. We shall omit
proofs of some of the relatively well known theorems stated below, referring the
reader to Curtis–Reiner [@bib:Curtis1962] or Bourbaki [@bib:Bourbaki1958] for
details.

A _minimal left ideal_ of $A$ is any minimal member of the set of nonzero left
ideals of $A$. Equivalently, a minimal left ideal is a simple submodule of
$lmodule(A, A)$.
#idx("minimal left ideal")

#theorem[
  Let $A$ be a left artinian ring. The following are equivalent:
  + $A$ is semisimple.
  + $A$ is a finite direct sum of minimal left ideals.
  + Every exact sequence of left $A$-modules is split.
  + Every left ideal of $A$ is a direct summand of $A$.
  + $A$ contains no nonzero nilpotent ideals.
  + Every left $A$-module is a direct sum of simple $A$-modules.
] <th:semisimple-artinian-structure>

Given a left artinian semisimple ring $A$, we may write
$A = L_1 plus.o dots.c plus.o L_r$, $L_i$ = minimal left ideal in $A$. Set
$
  1 = e_1 + dots.c + e_r, quad e_i in L_i.
$
From the equation $e_i = sum_j e_i e_j$ we deduce at once that
$
  e_i^2 = e_i, quad e_i e_j = 0 quad "for" quad i != j, quad L_i = A e_i.
$
Call ${e_i}$ a full system of _primitive idempotents_ of $A$. Let $B_1$ denote
the sum of those ${L_j}$ which are isomorphic to $L_1$, $B_2$ the sum of those
${L_j}$ isomorphic to a remaining summand (if any), and so on. Then we have
#idx("primitive idempotent")
$
  A = B_1 plus.o dots.c plus.o B_t
$
for some $t <= r$. It is easily shown (see references) that each $B_i$ is a
subring of $A$, and that $B_i dot B_j = 0$ for $i != j$, so $A$ is the ring
direct sum#footnote[The _ring direct sum_ $dsum_(i=1)^t B_i$ of the rings
  ${B_i}$ is defined to be the Cartesian product $B_1 times dots times B_t$,
  with componentwise addition and multiplication. This ring is in fact the
  _direct product_ (in the sense of category theory), and is often denoted by
  $product_(i=1)^t B_i$. We shall use the older terminology "ring direct sum"
  throughout this book.] of the ${B_i}$. Each $B_i$ is a _simple_ ring, that is,
a ring whose only two-sided ideals are 0 and $B_i$; #idx(
  "direct sum of rings",
)#idx("direct product of rings")#idx("simple ring") #source(100)of course, $B_i$
is left artinian (since $A$ is). Call these ${B_i}$ the _simple components_ of
$A$; they are uniquely determined inside $A$, although the ${L_i}$ are not.
Further, every simple $A$-module is isomorphic to a minimal left ideal of $A$,
hence to some minimal left ideal of some $B_i$.
#idx("simple components")

Conversely, if $B_1, dots, B_t$ are simple left artinian rings, then their ring
direct sum $dsum B_i$ is a semisimple left artinian ring whose simple components
are the ${B_i}$.

Now let $D$ be a _skewfield_ (or _division ring_), that is, a ring whose nonzero
elements form a multiplicative group. Denote by $M_n (D)$ the ring of all
$n times n$ matrices with entries in $D$. We call $M_n (D)$ a _full matrix
algebra_ over $D$. #idx("skewfield")#idx("division ring")#idx(
  "full matrix algebra",
)

Let $D^circle.stroked.tiny$ (or $D^"opp"$) denote the _opposite ring_ of $D$;
the elements of $D^circle.stroked.tiny$ are the symbols
${x^circle.stroked.tiny : x in D}$, with
#idx("opposite ring")
$
  (x^circle.stroked.tiny plus.minus y^circle.stroked.tiny)
  = (x plus.minus y)^circle.stroked.tiny, quad
  x^circle.stroked.tiny dot y^circle.stroked.tiny = (y x)^circle.stroked.tiny,
  quad x, y in D.
$
Then $D^circle.stroked.tiny$ is also a skewfield.

#theorem[
  + If $V = dsum_1^n D v_i$ is a left vector space over the skewfield $D$, then
    $Hom_D (V, V) tilde.equiv M_n (D^circle.stroked.tiny)$.
  + If $V = dsum_1^n v_i D$ is a right vector space over the skewfield $D$, then
    $Hom_D (V, V) tilde.equiv M_n (D)$.
] <th:endomorphisms-vector-space>

#proof[
  In case (i), for $a in Hom_D (V, V)$, let
  $
    a v_j = sum_(i=1)^n alpha_(i j) v_i, quad alpha_(i j) in D.
  $
  Then the desired isomorphism is given by
  $a -> (alpha_(i j)^circle.stroked.tiny)$.

  In case (ii), let
  $
    a v_j = sum_(i=1)^n v_i alpha_(i j), quad alpha_(i j) in D,
  $
  and let $a -> (alpha_(i j))$.
]

#theorem[
  For each $n$, the matrix ring $A = M_n (D)$ is a simple ring, both left and
  right artinian. Every minimal left ideal of $A$ is $A$-isomorphic to the left
  $A$-module $L$ of $n$-component column vectors with entries in $D$. Further,
  $M_n (D) tilde.equiv L^((n))$ as left $A$-modules and
  $D^circle.stroked.tiny tilde.equiv Hom_A (L, L)$. If we view $L$ as right
  $D$-space, then $A tilde.equiv Hom_D (L, L)$.
] <th:matrix-ring-simple>

#theorem(title: [Wedderburn Structure Theorem])[
  Every left artinian simple ring $A$ is isomorphic to an algebra of $n times n$
  matrices over a skewfield. The #source(101)ring $A$ determines $n$ uniquely,
  and determines the skewfield up to isomorphism. If $L$ is any minimal left
  ideal of $A$, then $D = Hom_A (L, L)$ is a skewfield, and
  $
    A = Hom_D (L, L) tilde.equiv M_n (D^circle.stroked.tiny),
  $
  where $n$ is the dimension of the left $D$-space $L$.
  #idx("Wedderburn Structure Theorem", target: [@th:wedderburn])
] <th:wedderburn>

#corollary[
  Every left artinian simple ring is also right artinian and is left and right
  noetherian. The same holds for left artinian semisimple rings.
] <cor:artinian-simple-two-sided>

By virtue of @cor:artinian-simple-two-sided, we may speak unambiguously of
artinian simple or semisimple rings, without having to distinguish between
"left" and "right". A quick proof of @th:wedderburn is sketched in
Exercise~@exc:wedderburn-milnor. See also Exercises~@exc:morita-wedderburn-a
and~@exc:morita-wedderburn-b.

=== Splitting fields <ss:splitting-fields>

Let $K$, $L$, $E$ denote fields, and $D$, $D'$ skewfields. The center of an
algebra $A$ will be denoted by $A^c$. A _central simple $K$-algebra_ is a simple
$K$-algebra $A$ for which $A^c = K$ and $(A : K)$ is finite. Call $D$ a
_skewfield over $K$_ if $D^c supset K$ and $(D : K)$ is finite. By Wedderburn's
Theorem, every central simple $K$-algebra $A$ is of the form $M_n (D)$ for some
skewfield $D$ over $K$. Further, #idx("central simple")#idx(
  "algebra",
  "central simple",
)#idx(
  "skewfield over $K$",
)
$
  A^c = {alpha I_n : alpha in D^c} tilde.equiv D^c,
$
so $D$ has center $K$, and $(A : K) = n^2 (D : K)$.

#theorem[
  Let $A$ be a central simple $K$-algebra, $B$ an artinian simple $K$-algebra,
  not necessarily finite dimensional over $K$. Then $B times.o_K A$ is an
  artinian simple algebra with center $B^c$.
] <th:tensor-central-simple>

#proof[
  We shall first compute $(B times.o A)^c$, where we write $times.o$ instead of
  $times.o_K$ for brevity. Let $B = dsum K e_i$, so
  $B times.o A = dsum e_i times.o A$. If
  $u = sum e_i times.o a_i in (B times.o A)^c$, then $u$ commutes with
  $1 times.o a$ for all $a in A$, whence $sum e_i times.o (a a_i - a_i a) = 0$.
  Therefore $a a_i = a_i a$ for all $a in A$, whence each $a_i in A^c = K$, and
  so $u = b_0 times.o 1$ for some $b_0 in B$. But now $u$ commutes with
  $b times.o 1$ for all $b in B$, whence $b_0 in B^c$. Identifying $B$ with
  $B times.o 1$ in $B times.o A$, we have thus shown that
  $(B times.o A)^c subset B^c$. The reverse inclusion is obvious, and therefore
  $(B times.o A)^c = B^c$.

  Since $B$ is artinian and $(A : K)$ is finite, it is clear that $B times.o A$
  is also artinian. It remains to show that $B times.o A$ is simple. We may
  write $B = M_r (D)$, $A = M_s (D')$, where $(D')^c = K$. Now for any
  skewfields $D$, $D'$ whose centers contain $K$, we have
  $
    M_r (D) times.o_K M_s (D')
    & tilde.equiv M_r (K) times.o M_s (K) times.o D times.o D' \
    & tilde.equiv M_(r s) (K) times.o (D times.o D')
    tilde.equiv M_(r s) (D times.o_K D').
  $ <eq:tensor-matrix-algebras>
  #source(102)Hence to prove that $B times.o A$ is simple, it suffices to prove
  that $D times.o D'$ is simple.

  Let $D = dsum K d_i$, so $D times.o D' = dsum d_i times.o D'$. Let $X != 0$ be
  a two-sided ideal of $D times.o D'$, and choose a shortest
  $x = sum_1^m d_i times.o delta_i$ in $X$, $delta_i in D'$. Then
  $x (1 times.o delta_1^(-1)) in X$, so after changing notation, we have
  $
    x = d_1 times.o 1 + sum_2^m d_i times.o delta_i in X.
  $
  Now let $delta in D'$, $delta != 0$; then
  $y = (1 times.o delta) dot x dot (1 times.o delta^(-1)) in X$, and
  $
    y = d_1 times.o 1 + sum_2^m d_i times.o delta delta_i delta^(-1).
  $
  Since $x - y in X$ and $x - y$ is shorter than $x$, this gives $y = x$.
  Therefore each $delta_i$ commutes with each nonzero $delta in D'$, whence each
  $delta_i in K$. Thus $x in D$, and so $x$ is a unit in $D times.o D'$, whence
  $X = D times.o D'$. This completes the proof.
]

#corollary[
  Let $A$ be a central simple $K$-algebra, $L supset K$. Then $L times.o_K A$ is
  a central simple $L$-algebra.
] <cor:central-simple-extension>

Let $A$ be any ring, $M$ a left $A$-module. Each $a in A$ determines a left
multiplication $a_L: m -> a m$, $m in M$. The map $a -> a_L$ is a ring
homomorphism of $A$ onto a subring $A_L$ of $Hom_bold(Z) (M, M)$. Call $M$ a
_faithful_ $A$-module if $A -> A_L$ is monic, that is, if $a dot M = 0$ implies
that $a = 0$.
#idx("faithful module")

We shall say that the pair $(A, M)$ has the _double centralizer property_ if
$A_L = Hom_D (M, M)$, where $D = Hom_A (M, M)$. It is trivially verified that
$(A, lmodule(A, A))$ has the double centralizer property, since in this case
$D = A_R$, the set of right multiplications by elements of $A$.
#idx("double centralizer property")

#theorem[
  + For each $A$-module $N$, the pair $(A, lmodule(A, A) dotplus N)$ has the
    double centralizer property.
  + Let $M$ be an $A$-module, $k$ a positive integer. If $(A, M^((k)))$ has the
    double centralizer property, then so does $(A, M)$.
] <th:double-centralizer-sums>

#proof[
  (i) Let $D = Hom_A (M, M)$, where $M = lmodule(A, A) dotplus N$. Each $d in D$
  is represented by a $2 times 2$ matrix $(d_(i j))$ of $A$-homomorphisms, where
  $
    d_11: A -> A, quad d_12: A -> N, quad d_21: N -> A, quad d_22: N -> N.
  $
  Now let $phi in Hom_D (M, M)$, and write $phi = (phi_(i j))$, a $2 times 2$
  matrix of additive homomorphisms. Since $phi$ commutes with the element
  $mat(1, 0; 0, 0)$ of $D$, it follows #source(103)that $phi_12 = 0$,
  $phi_21 = 0$. Next, fix $n_0 in N$, and define $d_(n_0) in D$ by
  $d_(n_0) (a, n) = (0, a n_0)$. Then
  $
    phi d_(n_0) (a, n) = phi(0, a n_0) = (0, phi_22 (a n_0)),
  $
  while
  $
    d_(n_0) phi(a, n) = d_(n_0) (phi_11 a, phi_22 n) = (0, (phi_11 a) n_0).
  $
  Thus $(phi_11 a) n_0 = phi_22 (a n_0)$ for all $(a, n_0) in M$, whence (taking
  $a = 1$) $(phi_11 (1)) n_0 = phi_22 (n_0)$. But $phi$ commutes with
  $mat(a_R, 0; 0, 0) in D$ for each $a in A$, whence $phi_11$ commutes with each
  $a_R$, and so $phi_11 = (a_0)_L$ for some $a_0 in A$. Thence
  $phi_22 (n_0) = a_0 n_0$, and so $phi$ is $(a_0)_L$ on $M$. This completes the
  proof of (i).

  To prove (ii), let $D = Hom_A (M, M)$, and let $V = M^((k))$ be the set of
  $1 times k$ row vectors with entries in $M$. If we think of $D$ as a domain of
  _right_ operators on $M$, then $M$ may be viewed as a bimodule
  $lmodule(A, M)_D$. In that case, $E = Hom_A (V, V) tilde.equiv M_k (D)$, and
  we may view $V$ as a bimodule $lmodule(A, V)_E$. Now let $f in Hom_D (M, M)$;
  we must prove that $f = a_L$ for some $a in A$. Define $f^*: V -> V$ by
  $
    f^* (m_1, dots, m_k) = (f m_1, dots, f m_k), quad m_i in M.
  $
  It is easily checked that $f^* in Hom_E (V, V)$. But $(A, V)$ has the double
  centralizer property, whence $f^* = a_L$ for some $a in A$. Then also
  $f = a_L$ (on $M$), as desired.
]

#corollary[
  Let $M$ be any faithful finitely generated left module over a semisimple
  artinian ring $A$. Then $(A, M)$ has the double centralizer property.
] <cor:double-centralizer-faithful>

#proof[
  Let $B_1, dots, B_t$ be the simple components of $A$, and let $M_i$ be a
  simple left $B_i$-module. Then by @th:semisimple-artinian-structure we may
  write $M = dsum_1^t M_i^((r_i))$. Since $B_j dot M_i = 0$ for $j != i$, and
  since $M$ is a faithful $A$-module, it follows that each $r_i > 0$. Further,
  we know that $B_i tilde.equiv M_i^((s_i))$ as left $B_i$-modules, for some
  $s_i$. It follows that if $k = max {s_i}$, then $lmodule(A, A)$ is a direct
  summand of the module $M^((k))$. Hence by @th:double-centralizer-sums[(i)] the
  pair $(A, M^((k)))$ has the double centralizer property, whence so does
  $(A, M)$ by @th:double-centralizer-sums[(ii)].
]

We are now ready to apply this corollary to the study of simple subalgebras of a
central simple algebra $A$, and eventually to the study of maximal subfields of
$A$. We begin with a fundamental result:

#theorem(major: true)[
  Let $K subset B subset A$, where $B$ is a simple subring of the central simple
  $K$-algebra $A$. Let
  #source(104)
  $
    B' = {x in A : x b = b x quad "for all" b in B},
  $
  the _centralizer_ of $B$ in $A$. Then $B'$ is a simple artinian ring, and $B$
  is its centralizer in $A$.
  #idx("centralizer")
] <th:double-centralizer>

#proof[
  Let $V$ be a simple left $A$-module, and let $D = Hom_A (V, V)$, viewed as
  left operator domain on $V$. Then $A = Hom_D (V, V)$, and $D$ is a skewfield
  with center $K$. For $a in A$, $d in D$, let $a_L$ and $d_L$ denote left
  multiplications on $V$. Then $b_L dot d_L = d_L dot b_L$ for all $b in B$,
  $d in D$, and therefore we may make $V$ into a left $D times.o_K B$-module by
  setting
  $
    (d times.o b) v = d_L b_L v, quad v in V.
  $
  By @th:tensor-central-simple, $D times.o_K B$ is a simple artinian algebra of
  finite $K$-dimension. Both $D_L$ and $B_L$ are $K$-subalgebras of
  $Hom_K (V, V)$, and the elements of $D_L$ commute with those of $B_L$. Hence
  the map $D times.o_K B -> D_L dot B_L$ is a $K$-algebra isomorphism (the
  kernel must be a two-sided ideal of $D times.o_K B$), and so letting $S$
  denote $D_L dot B_L$, it follows that $S$ is a simple algebra. Further, $V$ is
  a finitely generated faithful $S$-module, so the pair $(S, V)$ has the double
  centralizer property, by @cor:double-centralizer-faithful.

  Let $phi in Hom_S (V, V)$; then $phi in Hom_(D_L) (V, V) = A_L$, so
  $phi = a_L$ for some $a in A$ which centralizes $B_L$. Since both $A$ and $B$
  act faithfully on $V$, this shows that $a in B'$, and therefore
  $
    (B')_L = Hom_S (V, V).
  $
  Since $B' tilde.equiv (B')_L$, it follows from
  Exercise~@exc:endomorphisms-simple-artinian that $B'$ is a simple artinian
  ring. Further, since $(S, V)$ has the double centralizer property, we have
  $
    S = D_L dot B_L = Hom_((B')_L) (V, V).
  $ <eq:double-centralizer-s>
  Now let $x in A$ centralize $B'$; then $x_L$ centralizes $(B')_L$, so
  $x_L in S$ by @eq:double-centralizer-s. On the other hand, since $x_L in A_L$,
  it follows that $x_L$ centralizes $D_L$ in $S$. We now make use of the
  isomorphism $S tilde.equiv D times.o_K B$. The proof of
  @th:tensor-central-simple shows that the elements in $D times.o_K B$ which
  centralize $D times.o 1$ are contained in $D^c times.o B$, that is, in $B$
  itself (since $D^c = K$). Therefore $x_L in B_L$, whence $x in B$, as desired.
]

For later use, we give two important consequences of @eq:double-centralizer-s:

#corollary[
  Keeping the notation of @th:double-centralizer, let $V$ be a simple left
  $A$-module, and set $D = Hom_A (V, V)$. Then
  $
    D times.o_K B tilde.equiv Hom_(B') (V, V), quad
    (B : K)(B' : K) = (A : K).
  $
] <cor:centralizer-dimension>

#proof[
  The first assertion is a restatement of @eq:double-centralizer-s. To prove the
  second, let $W$ be a simple left $B'$-module. Since $V$ is a left $B'$-module,
  we have $V tilde.equiv W^((k))$ #source(105)where $k = dim V slash dim W$, and
  $dim$ denotes $dim_K$. Let $d_0 = dim D_0$, where $D_0 = Hom_(B') (W, W)$ is
  the skewfield part of $B'$. Let us write
  $
    dim D = d, quad dim V = d n, quad dim A = d n^2, \
    dim D_0 = d_0, quad dim W = d_0 m, quad dim B' = d_0 m^2,
  $
  for some $m$, $n$. Then
  $
    k = dim V slash dim W = d n slash d_0 m,
  $
  while from the first part of the corollary,
  $
    d dot dim B = dim Hom_(B') (W^((k)), W^((k))) = dim M_k (D_0) = k^2 d_0.
  $
  Consequently
  $
    (dim B)(dim B') & = (k^2 d_0 slash d) dot d_0 m^2 = k^2 d_0^2 m^2 slash d \
                    & = d^2 n^2 slash d = dim A,
  $
  which completes the proof.
]

#corollary[
  In the notation of @th:double-centralizer, we have
  $
    A times.o_K B^circle.stroked.tiny tilde.equiv M_r (B'), quad "where"
    quad r = (B : K).
  $
  Further, $B times.o_K B' tilde.equiv A$ if $B$ has center $K$.
] <cor:centralizer-tensor>

#proof[
  Keeping the terminology of the proof of @cor:centralizer-dimension, we have
  $A tilde.equiv M_n (D^circle.stroked.tiny)$, so
  $
    A times.o B^circle.stroked.tiny tilde.equiv
    M_n (D^circle.stroked.tiny times.o B^circle.stroked.tiny) tilde.equiv
    M_n ((D times.o B)^circle.stroked.tiny).
  $
  On the other hand $D times.o B tilde.equiv M_k (D_0)$, whence
  $A times.o B^circle.stroked.tiny tilde.equiv M_(k n) (D_0^"opp")$. Since
  $B' tilde.equiv M_m (D_0^"opp")$, we need only show that
  $dim B = k n slash m$. But this is clear, since
  $
    dim B = k^2 d_0 slash d = k dot (k d_0 slash d) = k dot (n slash m).
  $

  For the second part of the corollary, we observe that $B$ is a central simple
  $K$-algebra, and thus $B times.o B'$ is simple. Therefore the algebra
  homomorphism
  $
    B times.o_K B' -> B dot B' subset A
  $
  must be monic. Comparison of dimensions then shows that
  $B times.o B' tilde.equiv A$, and the corollary is established.
]

Now let $A = M_n (D)$ be a central simple $K$-algebra, where $D$ is a skewfield
with center $K$. We say that an extension field $E$ of $K$ _splits_ $A$, or is a
_splitting field_ for $A$, if
#idx("splitting field")
#source(106)
$
  E times.o_K A tilde.equiv M_r (E) quad "for some" r.
$
Since
$
  E times.o_K M_n (D) tilde.equiv M_n (E times.o_K D),
$
it follows from the uniqueness part of Wedderburn's Theorem that $E$ splits $A$
if and only if $E$ splits $D$. We may further remark that if $E$ splits $A$,
then so also does every field $Omega supset E$, since
$
  Omega times.o_K A tilde.equiv Omega times.o_E (E times.o_K A) tilde.equiv
  Omega times.o_E M_r (E) tilde.equiv M_r (Omega).
$

We are going to show that splitting fields always exist. Indeed, if $tilde(K)$
is any algebraic closure of $K$, then necessarily $tilde(K)$ splits $A$. To see
this, observe that $tilde(K) times.o_K A$ is a central simple
$tilde(K)$-algebra, hence is of the form $M_r (D')$ for some skewfield $D'$ over
$tilde(K)$. But then $D' = tilde(K)$, since each element of $D'$ is algebraic
over $tilde(K)$, and hence lies in $tilde(K)$ (see
Exercise~@exc:skewfield-over-algebraically-closed).

The important problem for us is to show the existence of splitting fields which
are finite separable extensions of $K$. This fact is contained in the following
basic result:

#theorem(major: true)[
  Let $D$ be a skewfield with center $K$, and let $(D : K)$ be finite.
  + Every maximal subfield $E$ of $D$ contains $K$, and is a splitting field for
    $D$. Further, if $m = (E : K)$, then
    $
      (D : K) = m^2, quad E times.o_K D tilde.equiv M_m (E).
    $
  + There exists a maximal subfield $L$ of $D$ which is separable over $K$.
] <th:maximal-subfields>

#proof[
  (i) Since $(D : K)$ is finite, $D$ contains maximal subfields. Let $E$ be a
  maximal subfield of $D$. Clearly $E supset K$, otherwise $E(K)$ is a larger
  subfield of $D$. Now choose $A = D$, $V = lmodule(D, D)$, $B = E$ in
  @th:double-centralizer. Obviously $B' supset E$, and equality must hold, since
  for each $x in B'$, $E(x)$ is a subfield of $D$ containing $E$. Thus
  $B' = B = E$, and @cor:centralizer-dimension becomes
  $
    D times.o_K E tilde.equiv Hom_E (V, V) tilde.equiv M_r (E), quad
    (E : K)^2 = (D : K),
  $
  where $r = (V : E)$. But
  $
    r^2 = (D times.o_K E : E) = (D : K) = (E : K)^2,
  $
  so $r = (E : K)$, and (i) is proved.

  (ii) We use induction on $(D : K)$, and let $(D : K) = n > 1$, the result
  being trivial when $n = 1$. It clearly suffices to handle the case where
  $op("char") K = p != 0$.

  Let us show first that $D$ contains a separable extension $E$ of $K$, with
  $E != K$. For each $x in D - K$ we have $K < K(x)$; call $x$ _purely
  inseparable_ over $K$ if $minpol_K x$ is of the form $X^(p^e) - a$ for some
  $a in K$. If $x$ is not purely inseparable, then
  #source(107)
  $
    minpol_K x = f(X^(p^e))
  $
  for some separable polynomial $f(X) in K[X]$. In this case, we need only
  choose $E = K(x^(p^e))$. So now suppose that each $x in D - K$ is purely
  inseparable over $K$. Then for each $x in D$, $minpol_K x$ is of the form
  $X^(p^e) - a$, $a in K$, $e >= 0$. We note that $p | n$, since $n$ is a
  multiple of $(K(x) : K)$ for each $x in D - K$. Choose $F$ to be any maximal
  subfield of $D$, so by (i) there is an isomorphism of $F$-algebras
  $
    mu: F times.o_K D tilde.equiv M_r (F) quad "for some" r.
  $
  Then $[mu(1 times.o x)]^(p^e) = mu(1 times.o x^(p^e)) = a dot I_r$, whence all
  of the characteristic roots of $mu(1 times.o x)$ are equal, and thus (since
  $p | n$) $op("Tr") mu(1 times.o x) = 0$. This holds for each $x in D$. But the
  matrices ${mu(1 times.o x) : x in D}$ form an $F$-basis for $M_r (F)$. Hence
  every matrix in $M_r (F)$ has zero trace, which is impossible. This completes
  the proof that there exists a field $E$ such that $K < E subset D$, $E$
  separable over $K$.

  Continuing with the proof, we let
  $
    D' = {x in D : a x = x a "for all" a in E},
  $
  the _centralizer_ of $E$ in $D$. Then $D'$ is a sub-skewfield of $D$, and we
  claim that $E$ is the center of $D'$. By @th:double-centralizer, $E$ is the
  centralizer of $D'$ in $D$. Any $x in (D')^c$ centralizes $D'$, hence lies in
  $E$. This proves that $(D')^c subset E$, and the reverse inclusion is obvious,
  because $D'$ centralizes $E$.

  We have thus obtained a central simple $E$-algebra $D'$, and
  $(D' : E) < (D : K)$. By the induction hypothesis, there is a maximal subfield
  $L$ of $D'$ such that $L$ is separable over $E$. Since $E$ is separable over
  $K$, it follows (by transitivity of separability) that $L$ is separable over
  $K$. Finally, we show that $L$ is a maximal subfield of $D$. If not, then
  there exists an $x in D - L$ centralizing $L$. Then $x$ centralizes $E$, so
  $x in D'$, and then $L < L(x) subset D'$, so $L(x)$ is a subfield of $D'$
  properly containing $L$. This is impossible, and therefore $L$ must be a
  maximal subfield of $D$, as desired. This completes the proof of the theorem.
]

To conclude this subsection, we present a basic result concerning the behavior
of $K$-algebras under separable extensions of the ground field:

#theorem[
  Let $L$ be a finite separable field extension of $K$, and let $A$ be a finite
  dimensional semisimple $E$-algebra, where $E$ is any field containing $K$
  (possibly $(E : K)$ is infinite). Then $L times.o_K A$ is also a finite
  dimensional semisimple $E$-algebra.
] <th:separable-extension-semisimple>

#proof[
  It is clear that $L times.o_K A$ is an $E$-algebra of dimension
  $(L : K)(A : E)$. It #source(108)suffices to prove the result when $A$ is a
  central simple $E$-algebra. We may write $L tilde.equiv K[X] slash (f(X))$,
  where $f(X)$ is an irreducible separable polynomial in $K[X]$. Let
  $f(X) = product f_i (X)$ be the factorization of $f(X)$ into irreducible
  polynomials in $E[X]$. Since $f(X)$ is separable, the ${f_i (X)}$ are
  distinct, and therefore
  $
    L times.o_K E tilde.equiv E[X] slash (f(X)) tilde.equiv
    dsum E[X] slash (f_i (X)).
  $
  Setting $F_i = E[X] slash (f_i (X))$, we see that each $F_i$ is a field
  containing $E$. Therefore
  $
    L times.o_K A tilde.equiv (L times.o_K E) times.o_E A tilde.equiv
    dsum F_i times.o_E A.
  $
  But now each $F_i times.o_E A$ is a central simple $F_i$-algebra by
  @cor:central-simple-extension, whence $L times.o_K A$ is a semisimple
  $E$-algebra, as claimed.
]

#corollary[
  Let $A$ be a finite dimensional $E$-algebra, where $E supset K$, and let $L$
  be a finite separable extension of $K$. Then
  $
    rad (L times.o_K A) = L times.o_K rad A.
  $
] <cor:radical-separable-extension>

#proof[
  Let $N = rad A$. Then $L times.o N$ is a nilpotent ideal of $L times.o A$,
  hence lies in $rad (L times.o A)$. On the other hand,
  $
    L times.o (A slash N) tilde.equiv (L times.o A) slash (L times.o N),
  $
  and $L times.o (A slash N)$ is semisimple by
  @th:separable-extension-semisimple. Hence
  $L times.o N supset rad (L times.o A)$, by
  Exercise~@exc:semisimple-quotient-contains-radical. Thus
  $L times.o N = rad (L times.o A)$, as claimed.
]

=== Separable algebras <ss:separable-algebras>

Throughout this section, let $K$, $E$, $L$ denote fields, $D$ and $D'$
skewfields, and $A$, $B$ finite dimensional $K$-algebras. If $L$ is a finite
extension of $K$, the assumption that $L$ be separable over $K$ has many
important consequences (see @th:integral-closure-finitely-generated,
@th:separable-extension-semisimple and @cor:radical-separable-extension, for
example). There is a more general concept of separability for $K$-algebras, and
in this section we shall present this definition and some of its consequences.
Indeed, one can even define separability of $R$-algebras, where $R$ is a
commutative ring (see for instance DeMeyer–Ingraham [@bib:DeMeyer1971] or
Exercise~@exc:separable-over-ring).

The most direct definition of separability is as follows: a _separable
$K$-algebra_ is a finite dimensional semisimple $K$-algebra $A$, such that the
center of each simple component of $A$ is a separable field extension of $K$.
Note that separability is not an intrinsic property of $A$, but depends on the
choice of ground field. If $(K : E)$ is finite and $A$ is $K$-separable, then
$A$ will be $E$-separable precisely when $K$ is separable over $E$. #idx(
  "separable algebra",
)#idx("algebra", "separable")

#source(109)
#theorem[
  Let $A$ be a finite dimensional $K$-algebra. The following statements are
  equivalent:
  + $A$ is a separable $K$-algebra.
  + There exists a finite separable field extension $E$ of $K$ such that
    $E times.o_K A$ is a direct sum of full matrix algebras over $E$.
  + For every field $F supset K$, $F times.o_K A$ is semisimple.
] <th:separable-criteria>

#proof[
  Let $A$ be a separable $K$-algebra with simple components $B_1, dots, B_t$,
  and let $K_i$ be the center of $B_i$, so $K_i$ is separable over $K$,
  $1 <= i <= t$. For each $i$, by @th:maximal-subfields we may choose a
  separable finite extension field $E_i$ of $K_i$ which splits $B_i$, say
  $
    E_i times.o_(K_i) B_i tilde.equiv M_(r_i) (E_i).
  $
  Let us set $K_i tilde.equiv K[X] slash (f_i (X))$, where $f_i (X)$ is a
  separable polynomial over $K$, and let $E'_i$ be the splitting field of
  $f_i (X)$ over $K$. Then $E'_i$ is a finite separable extension of $K$ for
  each $i$. By Exercise~@exc:common-extension-field, we can find a finite
  separable extension $E$ of $K$ which contains the fields
  $E_1, dots, E_t, E'_1, dots, E'_t$ (or, more precisely, $E$ contains
  $K$-isomorphic copies of the ${E_i}$ and ${E'_i}$). Therefore
  $
    E times.o_K K_i tilde.equiv E[X] slash (f_i (X)) tilde.equiv dsum E,
  $
  where the number of summands on the right equals the degree of $f_i (X)$. We
  then have $E times.o_K A = dsum E times.o_K B_i$, and
  $
    E times.o_K B_i & tilde.equiv (E times.o_K K_i) times.o_(K_i) B_i
                      tilde.equiv dsum E times.o_(K_i) B_i \
                    & tilde.equiv dsum E times.o_(E_i) (E_i times.o_(K_i) B_i)
                      tilde.equiv dsum E times.o_(E_i) M_(r_i) (E_i)
                      tilde.equiv dsum M_(r_i) (E).
  $
  This shows that (i) implies (ii).

  To prove that (ii) implies (iii), suppose that
  $
    E times.o_K A tilde.equiv dsum M_(r_i) (E),
  $
  and let $F supset K$. By Exercise~@exc:common-extension-field, we may find a
  field $L$ containing both $E$ and $F$, and then
  $
    L times.o_K A tilde.equiv L times.o_E (E times.o_K A) tilde.equiv
    dsum M_(r_i) (L).
  $
  On the other hand,
  $
    L times.o_K A tilde.equiv L times.o_F (F times.o_K A).
  $
  If $F times.o_K A$ were not semisimple, it would contain a nonzero nilpotent
  ideal $N$, and then $L times.o_F N$ would be a nonzero nilpotent ideal in the
  semisimple ring $L times.o_K A$. This is impossible, and so $F times.o_K A$ is
  semisimple, as claimed.

  Finally, we show that (iii) implies (i), by proving that if (i) is false, then
  so is (iii). If (i) is false, then either
  #source(110)
  #enum(
    numbering: "(a)",
    [$rad A != 0$, or],
    [$A$ is semisimple, but some $K_i$ is inseparable over $K$ (using the
      notation of the first part of the proof).],
  )
  In case (a), (iii) is false (just pick $F = K$!). In case (b), $K_i$ contains
  an element $y$ such that
  $
    minpol_K y = (X^p)^n + alpha_1 (X^p)^(n-1) + dots.c + alpha_n in K[X],
  $
  where $op("char") K = p != 0$. Choose $F$ to be the field
  $K(alpha_1^(1 slash p), dots, alpha_n^(1 slash p))$, and let
  $
    z = 1 times.o y^n + alpha_1^(1 slash p) times.o y^(n-1) + dots.c
    + alpha_n^(1 slash p) times.o 1 in F times.o_K K_i.
  $
  Then $z != 0$, since ${1, y, dots, y^n}$ are $K$-linearly independent elements
  of $K_i$. Further,
  $
    z^p = 1 times.o y^(p n) + alpha_1 times.o y^(p(n-1)) + dots.c
    + alpha_n times.o 1 = 0.
  $
  Thus $F times.o_K K_i$ contains a nonzero nilpotent element $z$. Since
  $
    F times.o_K B_i tilde.equiv (F times.o_K K_i) times.o_(K_i) B_i,
  $
  it follows that $z times.o 1$ is a nonzero nilpotent element in the center of
  $F times.o_K B_i$, and thus generates a nonzero nilpotent ideal in
  $F times.o_K B_i$. Therefore neither $F times.o_K B_i$ nor $F times.o_K A$ can
  be semisimple. This completes the proof of the theorem.
]

#corollary[
  If $A$ and $B$ are separable $K$-algebras, so is $A times.o_K B$.
] <cor:tensor-separable>

#proof[
  Choose fields $F$, $F'$ containing $K$ such that
  $
    F times.o_K A tilde.equiv M_r (F), quad
    F' times.o_K B tilde.equiv M_s (F'),
  $
  and then choose a field $E$ containing both $F$ and $F'$
  (Exercise~@exc:common-extension-field). Then
  $
    E times.o_K A tilde.equiv M_r (E), quad E times.o_K B tilde.equiv M_s (E),
  $
  and so by @eq:tensor-matrix-algebras
  $
    E times.o_K (A times.o_K B) tilde.equiv
    (E times.o_K A) times.o_E (E times.o_K B) tilde.equiv M_(r s) (E).
  $
  Thus $A times.o_K B$ is separable over $K$, as claimed.
]

Let $A^circle.stroked.tiny$ denote the _opposite ring_ of $A$, that is,
#idx("opposite ring")
$A^circle.stroked.tiny = {x^circle.stroked.tiny : x in A}$, with
$
  x^circle.stroked.tiny + y^circle.stroked.tiny
  = (x + y)^circle.stroked.tiny, quad
  x^circle.stroked.tiny dot y^circle.stroked.tiny = (y x)^circle.stroked.tiny,
  quad x, y in A.
$
Then $A$ and $A^circle.stroked.tiny$ have the same center. We set
$
  A^e = A times.o_K A^circle.stroked.tiny,
$
a finite dimensional $K$-algebra called the _enveloping algebra_ of $A$. We may
#idx("enveloping algebra")
#source(111)view $A$ as a left $A^e$-module, by means of the formula
$
  (x times.o y^circle.stroked.tiny) a = x a y, quad x, a in A, quad
  y^circle.stroked.tiny in A^circle.stroked.tiny.
$
(Indeed, every two-sided $A$-$A$-bimodule can be viewed as a left $A^e$-module.)
There is a left $A^e$-epimorphism
$
  mu: A^e -> A,
$
defined by setting $mu(x times.o y^circle.stroked.tiny) = x y$. Clearly $A$ is a
projective left $A^e$-module if and only if there exists a map
$nu in Hom_(A^e) (A, A^e)$ such that $mu dot nu = 1$. It is obvious that such a
map $nu$ exists if and only if for each $K$-basis ${x_1, dots, x_n}$ of $A$,
there exist elements ${y_i}$ of $A$ such that
+ $sum x_i y_i = 1$, and
+ For each $a in A$, if $a x_i = sum alpha_(i j) x_j$, $1 <= i <= n$, with the
  ${alpha_(i j)} in K$, then $y_i a = sum alpha_(j i) y_j$, $1 <= i <= n$.
Indeed, once $nu$ is given, we set
$nu(1) = sum_(i=1)^n x_i times.o y_i^circle.stroked.tiny$; condition (i) asserts
that $mu dot nu = 1$, while (ii) asserts that $nu$ is an $A^e$-homomorphism.
Conversely, given a $K$-basis ${x_i}$ of $A$, and given elements ${y_i} in A$
satisfying (i) and (ii), we need only set
$nu(a) = a dot sum x_i times.o y_i^circle.stroked.tiny$, $a in A$.

#theorem[
  Let $A$ be a finite dimensional $K$-algebra. Then $A$ is a separable
  $K$-algebra if and only if $A$ is $A^e$-projective.
] <th:separable-projective-enveloping>

#proof[
  If $A$ is $K$-separable, so is $A^circle.stroked.tiny$, and thus $A^e$ is
  $K$-separable by @cor:tensor-separable. In particular, then, $A^e$ is
  semisimple, and so _every_ $A^e$-module is projective. Conversely, suppose
  that $A$ is $A^e$-projective. We shall prove that $A$ is $K$-separable by
  showing that $B = F times.o_K A$ is semisimple for each field $F supset K$. We
  have
  $
    B^e & = B times.o_F B^circle.stroked.tiny
          = (F times.o_K A) times.o_F (F times.o A^circle.stroked.tiny) \
        & tilde.equiv F times.o_K (A times.o_K A^circle.stroked.tiny)
          = F times.o_K A^e.
  $
  Let $mu' = 1 times.o mu: F times.o_K A^e -> F times.o_K A$, and likewise let
  $nu' = 1 times.o nu$. Then $nu'$ is a $B^e$-homomorphism such that
  $mu' dot nu' = 1$; let us set
  $
    nu'(1) = sum x_i times.o y_i^circle.stroked.tiny, quad x_i, y_i in B,
  $
  so $sum x_i y_i = 1$.

  In order to prove that $B$ is semisimple, we show that if $N subset M$ are
  left $B$-modules, then $N$ is a direct summand of $M$. We may view
  $Hom_K (M, M)$ as a $B$-$B$-bimodule, hence as a left $B^e$-module, with
  $
    (x times.o y^circle.stroked.tiny) f = x f y, quad x, y in B, quad
    f in Hom_K (M, M).
  $
  #source(112)Let $pi: M -> N$ be a $K$-projection of $M$ onto $N$, so
  $pi^2 = pi$. We set
  $
    pi' = nu'(1) dot pi = sum x_i pi y_i.
  $
  Since $pi = 1$ on $N$, for each $n in N$ we have
  $
    pi'(n) = sum x_i pi(y_i n) = sum x_i y_i n = n,
  $
  whence $(pi')^2 = pi'$. Finally, for $b in B$ we have
  $
    b pi' & = (b times.o 1) dot nu'(1) pi
            = nu'((b times.o 1) dot 1) pi \
          & = nu'((1 times.o b^circle.stroked.tiny) dot 1) pi
            = (1 times.o b^circle.stroked.tiny) pi' = pi' b.
  $
  Thus $pi'$ is a $B$-homomorphism, whence $N$ is a $B$-direct summand of $M$ as
  claimed, and the theorem is proved.
]

=== Skolem–Noether Theorem <ss:skolem-noether>

Throughout this subsection, $A$ denotes a central simple $K$-algebra. Each
invertible element $a in A$ determines an inner automorphism of $A$, given by
$x -> a x a^(-1)$, $x in A$, and this automorphism fixes each element of $K$.
The Skolem–Noether Theorem, to be proved below, asserts the converse: every
algebra automorphism of $A$ fixing each element of $K$ must be an inner
automorphism. We shall prove a slightly more general version of this result,
namely:
#idx("inner automorphism")

#theorem(major: true, title: [Skolem–Noether])[
  Let $K subset B subset A$, where $B$ is a simple subring of the central simple
  $K$-algebra $A$. Then every $K$-isomorphism $phi$ of $B$ onto a subalgebra
  $tilde(B)$ of $A$ extends to an inner automorphism of $A$, that is, there
  exists an invertible $a in A$ such that
  $
    phi(b) = a b a^(-1), quad b in B.
  $
  #idx("Skolem–Noether Theorem", target: [@th:skolem-noether])
] <th:skolem-noether>

#proof[
  Let $times.o$ stand for $times.o_K$ throughout this proof, and let us use the
  notation introduced in the first paragraph of the proof of
  @th:double-centralizer. We have seen there that a simple left $A$-module $V$
  is a left $D times.o B$-module, under the action
  $
    (d times.o b) v = d dot b dot v, quad v in V.
  $
  In the same way, we may view $V$ as left $D times.o tilde(B)$-module.

  We now make use of the structure of $V$ as left $D times.o tilde(B)$-module,
  together with the $K$-algebra isomorphism
  $
    1 times.o phi: D times.o B tilde.equiv D times.o tilde(B),
  $
  to define an action (denoted by $*$) of $D times.o B$ on $V$. We then obtain a
  left $D times.o B$-module $tilde(V)$, having the same elements as $V$, but
  with the action of #source(113)$D times.o B$ on $tilde(V)$ given by
  $
    (d times.o b) * v = d dot phi(b) dot v, quad v in V.
  $
  Then $V$ and $tilde(V)$ are a pair of left modules over the simple artinian
  ring $D times.o B$, and have the same $K$-dimension. It follows at once that
  there is a left $D times.o B$-isomorphism $theta: V tilde.equiv tilde(V)$. In
  other words, there is an isomorphism $theta in Hom_K (V, V)$ such that
  $
    theta(d dot b dot v) = (d times.o b) * theta(v)
    = d dot phi(b) dot theta(v), quad v in V.
  $ <eq:skolem-noether-theta>
  Taking $b = 1$, it follows that $theta in Hom_D (V, V) = A$, so $theta$ is
  given by a left multiplication by an element $a in A$. Since $theta$ is an
  isomorphism, $a$ is invertible. Formula @eq:skolem-noether-theta becomes
  $
    a dot (d dot b dot v) = d dot phi(b) dot a v, quad v in V.
  $
  If we put $d = 1$, and remember that $A$ acts faithfully on $V$, we may
  conclude that
  $
    a dot b = phi(b) dot a, quad b in B,
  $
  which proves the theorem.
]

#corollary[
  + Every $K$-automorphism of $A$ is inner.
  + Any two $K$-isomorphic subfields $L$ and $L'$ of $A$ are conjugate, that is,
    $L' = a L a^(-1)$ for some invertible $a in A$.
] <cor:automorphisms-inner>

#theorem(major: true, title: [Wedderburn])[
  Every finite skewfield is a field.
  #idx(
    "Wedderburn Theorem on finite skewfields",
    target: [@th:finite-skewfield],
  )
] <th:finite-skewfield>

#proof[
  Let $D$ be a finite skewfield with center $K$, and let $D^* = D - {0}$,
  $K^* = K - {0}$. If $L$ is a maximal subfield of $D$, then $(D : K) = n^2$,
  $(L : K) = n$. Any other maximal subfield $L'$ is a finite field, and
  $(L' : K) = n$, so $card L = card L'$. Thus $L'$ is $K$-isomorphic to $L$,
  whence by @cor:automorphisms-inner $L'$ is conjugate to $L$. Since every
  $x in D$ lies in a subfield $K(x)$ of $D$, and hence in some maximal subfield,
  we conclude that
  $
    D^* = union.big a L^* a^(-1),
  $ <eq:skewfield-union-of-conjugates>
  where $a$ ranges over some set of invertible elements of $D$. But for
  $x in L^*$,
  $
    (a x) L^* (a x)^(-1) = a L^* a^(-1),
  $
  so in @eq:skewfield-union-of-conjugates it suffices to let $a$ range over the
  left coset representatives of $L^*$ in $D^*$. Hence there are $(D^* : L^*)$
  sets ${a L^* a^(-1)}$ occurring in @eq:skewfield-union-of-conjugates, each of
  cardinality $card L^*$; these sets are _not_ disjoint, since each contains 1.
  Thus $D^*$ cannot be their union, unless there is only one such set, that is,
  $D^* = L^*$. Thus $D = L = K$, as desired.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  #source(114)Prove Schur's Lemma: if $M$ is a simple left $A$-module, then
  $Hom_A (M, M)$ is a skewfield.
  #idx("Schur's Lemma")
  #hint[@exc:schur-lemma][For each nonzero $f in Hom_A (M, M)$, both $ker f$ and
    $im f$ are submodules of $M$, and so $ker f = 0$, $im f = M$.]
  <hint:schur-lemma>
] <exc:schur-lemma>

#exercise[
  Let $V^((k))$ be the direct sum of $k$ copies of the left $A$-module $V$, and
  let $E = Hom_A (V, V)$. Prove that
  $
    Hom_A (V^((k)), V^((k))) tilde.equiv M_k (E).
  $
] <exc:endomorphisms-of-power>

#exercise(tag: "2a")[
  Let $M$ be a finitely generated left $A$-module, where $A$ is a simple
  artinian ring. Show that $Hom_A (M, M)$ is also a simple artinian ring.
  #hint[@exc:endomorphisms-simple-artinian][Write $M tilde.equiv V^((k))$, where
    $V$ is a simple left $A$-module. Then use the preceding exercises and
    @th:matrix-ring-simple.]
  <hint:endomorphisms-simple-artinian>
] <exc:endomorphisms-simple-artinian>

#exercise(tag: "2b")[
  Prove that the result in Exercise~@exc:endomorphisms-simple-artinian remains
  valid when "simple" is replaced by "semisimple".
] <exc:endomorphisms-semisimple-artinian>

#exercise[
  Let $A$ be a ring direct sum $dsum_(i=1)^t B_i$, where each $B_i$ is a ring
  having no two-sided ideals except 0 and $B_i$. Show that every two-sided ideal
  $J$ of $A$ is a subsum $dsum B_(i_nu)$.
  #hint[@exc:ideals-of-direct-sum][$J dot B_i = 0$ or $B_i$ for each $i$, and
    $J = dsum J B_i$.] <hint:ideals-of-direct-sum>
] <exc:ideals-of-direct-sum>

#exercise[
  Let $L$ be a minimal left ideal of the simple left artinian ring $A$, and let
  $D = Hom_A (L, L)$. Show that $A = Hom_D (L, L)$. Using
  Exercises~@exc:schur-lemma and~@exc:endomorphisms-of-power, prove that $D$ is
  a skewfield, and that $A tilde.equiv M_n (D^circle.stroked.tiny)$, where $n$
  is the dimension of $L$ as left $D$-space.
  #hint[@exc:wedderburn-milnor][This is the harder part of the Wedderburn
    Structure Theorem @th:wedderburn. The following quick proof is due to Milnor
    [@bib:Milnor1971]. Since $L dot A$ is a two-sided ideal of $A$, we have
    $L dot A = A$. Let
    $
      1 = sum_(i=1)^m l_i a_i, quad l_i in L, quad a_i in A,
    $
    with $m$ minimal. There is a left $A$-epimorphism $L^((m)) -> A$, given by
    $(x_1, dots, x_m) -> sum_1^m x_i a_i$. The map is monic, since if
    $sum x_i a_i = 0$ with (say) $x_1 != 0$, then $A x_1 = L$ implies that
    $
      L a_1 = A x_1 a_1 subset L a_2 + dots.c + L a_m,
    $
    contradicting the minimality of $m$. Thus $A tilde.equiv L^((m))$ as left
    $A$-modules, whence
    $
      A^circle.stroked.tiny tilde.equiv Hom_A (A, A) tilde.equiv
      Hom_A (L^((m)), L^((m))) tilde.equiv M_m (D),
    $
    so $A tilde.equiv M_m (D^circle.stroked.tiny)$. Note that $m = n$.]
  <hint:wedderburn-milnor>
] <exc:wedderburn-milnor>

#exercise[
  Let $A$ be a semisimple finite dimensional $K$-algebra, and let $E$ be a
  separable algebraic extension field of $K$, that is, for each field $L$ with
  $K subset L subset E$, $(L : K)$ finite, the extension $L slash K$ is
  separable. Prove that $E times.o_K A$ is semisimple.
  #hint[@exc:separable-algebraic-extension][Let $N = rad (E times.o_K A)$. For
    each $L$, $N inter (L times.o_K A)$ is a nilpotent ideal of $L times.o_K A$,
    hence is zero. But each $x in N$ lies in some
    $L times.o_K A$.] <hint:separable-algebraic-extension>
] <exc:separable-algebraic-extension>

#exercise[
  Let $L_1, dots, L_n$ be a set of field extensions of $K$. Show that there
  exists a field $Omega$ containing $K$, for which there exist $K$-isomorphisms
  $mu_i: L_i -> Omega$, $1 <= i <= n$. Further, if each $(L_i : K)$ is finite,
  the field $Omega$ may be chosen so that $(Omega : K)$ is finite. If in
  addition #source(115)each $L_i$ is separable over $K$, then $Omega$ may be
  chosen finite separable over $K$.
  #hint[@exc:common-extension-field][Let
    $A = L_1 times.o_K dots.c times.o_K L_n$, a commutative $K$-algebra. By
    Zorn's Lemma, $A$ has a maximal ideal $M$. Set $Omega = A slash M$, a field
    containing $K$, and define $mu_i$ by composition of maps:
    $L_i -> A -> Omega$. If each $(L_i : K)$ is finite, so is $(Omega : K)$. If
    each $L_i$ is finite separable over $K$, then by @cor:tensor-separable $A$
    is a direct sum of fields $Omega_j$, each of which is a finite separable
    extension of $K$, and we may pick $Omega$ to be any $Omega_j$.]
  <hint:common-extension-field>
] <exc:common-extension-field>

#exercise[
  Let $A$ be a separable $K$-algebra, $B$ any semisimple finite dimensional
  $K$-algebra. Prove that $A times.o_K B$ is semisimple.
  #hint[@exc:separable-times-semisimple][We may assume that both $A$ and $B$ are
    simple, and set $L = A^c$, $E = B^c$. As in the proof of
    @th:separable-extension-semisimple, we have
    $L times.o_K E tilde.equiv dsum F_i$, since $L$ is separable over $K$, where
    each $F_i$ is a field containing $K$-isomorphic copies of $L$ and $E$. Hence
    $
      A times.o_K B tilde.equiv A times.o_L (L times.o_K E) times.o_E B
      tilde.equiv dsum (A times.o_L F_i) times.o_E B.
    $
    But $A times.o_L F_i$ is a central simple $F_i$-algebra, and $B$ is a
    central simple $E$-algebra, so each summand $(A times.o_L F_i) times.o_E B$
    is simple by @th:tensor-central-simple.] <hint:separable-times-semisimple>
] <exc:separable-times-semisimple>

#exercise[
  Let $G = {g_1, dots, g_n}$ be a finite group of order $n$, and let $K$ be a
  field. Show that the group algebra $K G$ is a separable $K$-algebra if and
  only if $op("char") K divides.not n$. #idx("separable algebra")#idx(
    "algebra",
    "separable",
  ) #hint[@exc:group-algebra-separable][If $op("char") K | n$, then
    $sum_1^n g_i$ is a nilpotent element in the center of $K G$, so $K G$ is not
    semisimple. If $op("char") K divides.not n$, set $A = K G$, and define
    $nu: A -> A times.o_K A^circle.stroked.tiny = A^e$ by
    $
      nu(1) = n^(-1) sum_i g_i times.o g_i^(-1),
    $
    $nu(a) = a dot nu(1)$, $a in A$. Show that $nu$ is an $A^e$-homomorphism
    such that $mu nu = 1$, where $mu: A^e -> A$ is as in
    §~@ss:separable-algebras.] <hint:group-algebra-separable>
] <exc:group-algebra-separable>

#exercise[
  Let $Lambda$ be an $R$-algebra, where $R$ is a commutative ring. Call $Lambda$
  _$R$-separable_ if $Lambda$ is $Lambda^e$-projective, where
  $Lambda^e = Lambda times.o_R Lambda^circle.stroked.tiny$. Show that if
  $Lambda$ is $R$-separable, then every $R$-projective $Lambda$-module is
  $Lambda$-projective. #hint[@exc:separable-over-ring][Imitate the proof of
    @th:separable-projective-enveloping.] <hint:separable-over-ring>
] <exc:separable-over-ring>

#exercise[
  Let $R$ be a commutative ring, $G$ a group of order $n$. Show that $R G$ is
  $R$-separable if $n$ is a unit in $R$.
] <exc:group-ring-separable>

#exercise[
  Let $e$, $e'$ be idempotents in the simple artinian ring $A$, such that
  $A e tilde.equiv A e'$ as left $A$-modules. Show that there exists a unit
  $u in A$ such that $e' = u e u^(-1)$.
  #hint[@exc:conjugate-idempotents][Let $A = Hom_D (V, V)$, where $V$ is a right
    vector space over the skewfield $D$. Since $V = e V plus.o (1 - e) V$ is a
    $D$-decomposition of $V$, then relative to a suitable $D$-basis of $V$, $e$
    is represented by a diagonal matrix $diag(1, dots, 1, 0, dots, 0)$. The same
    holds for $e'$, with the same number of 1’s, since $A e tilde.equiv A e'$.
    If $u in A$ gives a suitable change of $D$-bases of $V$, then
    $e' = u e u^(-1)$.]
  <hint:conjugate-idempotents>
] <exc:conjugate-idempotents>

#exercise[
  If $e$ is a primitive idempotent of the simple artinian ring $A$, show that
  $A e$ is a minimal left ideal of $A$, and $A(1 - e)$ a maximal left ideal.
  Further, let $A x$ be a maximal left ideal of $A$. Show that $x A$ is a
  maximal right ideal. Prove that if $A x$ and $A y$ are any pair of maximal
  left ideals in $A$, then $u dot A x dot u^(-1) = A y$ for some unit $u in A$.
  #hint[@exc:maximal-ideals-conjugate][Let $A x$ be maximal, and write
    $A = A e plus.o A x$ with $e$ a primitive idempotent. Set $1 = e + a x$,
    $a in A$. Then $A = e A plus.o a x A$, so $a x A$ is a maximal right ideal.
    But $a x A$ is a homomorphic image of $x A$, and $x A != A$, whence $x A$ is
    also a maximal right ideal. Further, if $e$ and $e'$ are primitive
    idempotents of $A$, then $e' = u e u^(-1)$ for some unit #source(
      116,
    )$u in A$, by Exercise~@exc:conjugate-idempotents. But every maximal left
    ideal of $A$ is of the form $A(1 - e)$ for some primitive idempotent
    $e$.] <hint:maximal-ideals-conjugate>
] <exc:maximal-ideals-conjugate>

#exercise[
  Let $A$ be a separable $K$-algebra, $L$ any extension field of $K$. Show that
  $L times.o_K A$ is a separable $L$-algebra.
  #hint[@exc:separable-base-change][For any field $F supset L$, we have
    $
      F times.o_L (L times.o_K A) tilde.equiv F times.o_K A,
    $
    and the latter is semisimple by @th:separable-criteria.]
  <hint:separable-base-change>
] <exc:separable-base-change>

#exercise[
  Let the separable $K$-algebra $A$ have simple components ${A_i}$, and let
  $K_i$ be the center of $A_i$. Let $F$ be a field containing $K$, where
  possibly $(F : K)$ is infinite. Prove that there is an $F$-algebra isomorphism
  $
    F times.o_K A tilde.equiv dsum_i dsum_j F_(i j) times.o_(K_i) A_i,
  $
  where each $F_(i j)$ is a field containing $K$-isomorphic copies of $K_i$ and
  $F$, and where $(F_(i j) : F)$ is finite. Show that each summand
  $F_(i j) times.o_(K_i) A_i$ is a central simple $F_(i j)$-algebra.
  #hint[@exc:separable-extension-decomposition][We have
    $
      F times.o_K A tilde.equiv dsum_i (F times.o_K K_i) times.o_(K_i) A_i.
    $
    Since $K_i slash K$ is finite separable, the $F$-algebra $F times.o_K K_i$
    is semisimple by @th:separable-extension-semisimple, hence is expressible as
    a direct sum of fields $F_(i j)$. Each $F_(i j)$ contains $K$-isomorphic
    copies of $F times.o 1$ and $1 times.o K_i$.]
  <hint:separable-extension-decomposition>
] <exc:separable-extension-decomposition>
