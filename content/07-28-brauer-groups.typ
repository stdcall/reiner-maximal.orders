#import "main-defs.typ": *
#import "statements.typ": *

== Brauer groups <sec:brauer-groups>

Throughout this section let $K$, $L$, and $E$ denote fields, with $K subset L$,
and let $D$ denote a skewfield. The symbols $A$ and $B$ will always denote
central simple $K$-algebras. If $A tilde.equiv M_r (D)$, we shall refer to $D$
as the _skewfield part_#idx("skewfield part") of $A$. We shall call $A$ and $B$
_similar_#idx("similar algebras") (notation: $A tilde.op B$) if their skewfield
parts are $K$-isomorphic#footnote[Two $K$-algebras $X$, $Y$ are _$K$-isomorphic_
  if there exists a ring isomorphism $phi: X tilde.equiv Y$ such that
  $phi(alpha x) = alpha phi(x)$, $alpha in K$, $x in X$.]<fn:k-isomorphic>. By
Wedderburn's Theorem @th:wedderburn, $A tilde.op B$ if and only if there is an
isomorphism of $K$-algebras#footnote(<fn:k-isomorphic>)
$
  A times.o_K M_r (K) tilde.equiv B times.o_K M_s (K)
$
for some integers $r$, $s$.

Let $[A]$ denote the similarity class of $A$. For each $A$ and $B$ (always
assumed to be central simple $K$-algebras), the tensor product $A times.o_K B$
is also a central simple $K$-algebra by @th:tensor-central-simple. Let us define
multiplication of classes by the formula
$
  [A][B] = [A times.o_K B].
$ <eq:brauer-class-product>
Then, by @eq:tensor-matrix-algebras, multiplication of classes is well defined.
Clearly
#source(247)
$
  [A][B] = [B][A], quad [A][K] = [A].
$
Finally, we remark that if $A$ is a central simple $K$-algebra, then so is its
opposite ring $A^circle.stroked.tiny$.

#theorem[
  The classes of central simple $K$-algebras form an abelian group $B(K)$,
  called the _Brauer group_#idx("Brauer group") of $K$, relative to the
  multiplication defined in @eq:brauer-class-product. The identity class is
  $[K]$, and the inverse of $[A]$ is $[A^circle.stroked.tiny]$.
] <th:brauer-group>

#proof[
  Since the associative law holds for tensor products, it also holds for
  multiplication of similarity classes. Clearly $[K]$ acts as identity, and we
  need only prove that $[A][A^circle.stroked.tiny] = [K]$. We choose $B = A$ in
  @cor:centralizer-tensor, so then $B' = K$. By @cor:centralizer-tensor, we
  obtain
  $
    A times.o_K A^circle.stroked.tiny tilde.equiv M_n (K), quad n = (A : K),
  $
  and thus
  $
    [A][A^circle.stroked.tiny] = [M_n (K)] = [K].
  $
  This completes the proof.
]

#theorem[
  Let $K subset L$. There is a homomorphism of groups
  $
    B(K) -> B(L), quad [A] -> [L times.o_K A], quad [A] in B(K).
  $
] <th:brauer-group-extension-map>

#proof[
  As usual, let $A$ and $B$ denote central simple $K$-algebras. Then
  $L times.o_K A$ is a central simple $L$-algebra by
  @cor:central-simple-extension. It is easily verified that
  $
    A tilde.op B ==> L times.o_K A tilde.op L times.o_K B, \
    L times.o_K (A times.o_K B) tilde.equiv
    (L times.o_K A) times.o_L (L times.o_K B), quad
    L times.o_K A^circle.stroked.tiny tilde.equiv
    (L times.o_K A)^circle.stroked.tiny,
  $
  which imply the desired result.
]

Keeping the above notation, let $B(L slash K)$ be the kernel of the homomorphism
$B(K) -> B(L)$. Thus $[A] in B(L slash K)$ if and only if
$L times.o_K A tilde.equiv M_r (L)$ for some $r$. (In this case we say that $L$
_splits_ $A$, or is a _splitting field_ for $A$.) There is an exact sequence of
groups
$
  1 -> B(L slash K) -> B(K) -> B(L)
$ <eq:relative-brauer-group-sequence>
whenever $K subset L$.

The next set of theorems will show that each class $[A'] in B(L slash K)$
contains a representative $A$ in which $L$ is embedded as a maximal subfield. In
§~@sec:crossed-product-algebras, we shall see that such algebras $A$ can be
described explicitly as crossed-products.

#theorem(major: true)[
  Let $D$ be a skewfield with center $K$, and let $m = sqrt((D : K))$ be the
  _index_#idx("index (of skewfield)") of $D$. Let $E$ be a finite extension of
  $K$.
  + #source(248)If $E$ splits $D$, then $m | (E : K)$.
  + There exists a smallest positive integer $r$ for which there is an embedding
    $E subset M_r (D)$ as $K$-algebras. With this choice of $r$, $E$ splits $D$
    if and only if $E$ is a maximal subfield of $M_r (D)$. Furthermore, the
    centralizer $E'$ of $E$ in $M_r (D)$ is a skewfield, and $E$ is a maximal
    subfield of $M_r (D)$ if and only if $E = E'$.
] <th:splitting-field-matrix-embedding>

#proof[
  Let $S = E times.o_K D$, a central simple $E$-algebra, and let $V$ be a simple
  right $S$-module. Then $V$ is a right vector space over the skewfield $D$, say
  $(V : D) = r$, and there is an embedding of $K$-algebras
  $
    E subset Hom_D (V, V) tilde.equiv M_r (D),
  $ <eq:minimal-embedding>
  since $E$ and $D$ commute elementwise in $S$. Let us show that this gives an
  embedding with minimal $r$. Indeed, given any embedding $E subset M_t (D)$,
  there is a right $D$-space $W$ of dimension $t$ over $D$, such that
  $E subset Hom_D (W, W)$. By Exercise~@exc:tensor-product-module, $W$ may be
  viewed as a right $(E times.o_K D)$-module, and hence $W$ is isomorphic to a
  direct sum of copies of $V$. Hence $t$ is a multiple of $r$. This proves that
  the embedding given in @eq:minimal-embedding has minimal $r$.

  Keeping this notation, let $E'$ be the centralizer#footnote[See
    page~@th:double-centralizer[page].] of $E$ in the central simple $K$-algebra
  $B = Hom_D (V, V)$. Each $f in E'$ is then an $(E times.o_K D)$-endomorphism
  of $V$, that is, $f in Hom_S (V, V)$. Conversely, it is clear that
  $Hom_S (V, V) subset E'$. This shows that $E' = Hom_S (V, V)$, and the latter
  is a skewfield by Schur's Lemma (see Exercise~@exc:schur-lemma). We have now
  proved that $E'$ is a skewfield containing $E$. Let us deduce at once that
  $E' = E$ if and only if $E$ is a maximal subfield of $B$. Obviously, if
  $E' = E$ then $E$ must be a maximal subfield of $B$. On the other hand, if
  $E' > E$, choose any $x in E' - E$. Since $E'$ centralizes $E$, the element
  $x$ commutes with each element of $E$. Therefore $E(x)$ is a field (since it
  is contained in the skewfield $E'$), and $E(x) > E$. Thus if $E' > E$, then
  $E$ is not a maximal subfield of $B$. We also observe that by
  @cor:centralizer-dimension we have
  $
    (E : K)(E' : K) = (B : K) = m^2 r^2,
  $ <eq:centralizer-dimension-product>
  whether or not $E' = E$.

  After these preliminaries, let us turn to the proof of (i). Suppose that $E$
  splits $D$; then $S = E times.o_K D tilde.equiv M_m (E)$, so
  $S tilde.equiv V^((m))$ as right $S$-modules. Comparing dimensions as right
  $D$-spaces, we obtain
  $
    m r = m(V : D) = (S : D) = (E : K).
  $ <eq:splitting-field-dimension>
  Therefore $m | (E : K)$, which proves (i). Furthermore, since $E' supset E$,
  it follows from @eq:centralizer-dimension-product that $E' = E$. Thus $E$ is a
  maximal subfield of $B$, which proves part of (ii).

  We now drop the assumption that $E$ splits $D$, and we show finally that if
  $E$ is a maximal subfield of $B$, then necessarily $E$ splits $D$. Indeed, if
  $E$ is a maximal #source(249)subfield of $B$, then we have seen that $E' = E$.
  On the other hand, by @cor:centralizer-tensor we have
  $
    B times.o_K E^circle.stroked.tiny tilde.equiv M_s (E'), quad s = (E : K).
  $
  Since $E = E^circle.stroked.tiny = E'$, this shows that $E$ splits $B$. But
  $B tilde.equiv M_r (D)$, and so $E$ also splits $D$. This completes the proof
  of the theorem.
]

#remark(kind: "Remarks")[
  If $D$ is a skewfield with center $K$ and index $m$, then we know from
  @th:maximal-subfields that every maximal subfield of $D$ splits $D$, and has
  $K$-dimension $m$. Part (i) of the preceding theorem asserts that we cannot
  find any smaller extensions of $K$, whether contained in $D$ or not, which
  split $D$. Thus @th:maximal-subfields is a "best possible" result.

  The preceding theorem shows that if $E$ splits $D$, then $E$ can be embedded
  in a full matrix algebra $B$ over $D$, in such a way that
  $
    (B : K) = (E : K)^2,
  $
  and that $E$ coincides with its centralizer in $B$. We shall call $E$ a
  _self-centralizing maximal subfield_ of $B$.
  #idx("self-centralizing maximal subfield")
] <rem:self-centralizing-maximal-subfield>

We conclude with some easy consequences of the preceding discussion.

#corollary[
  Let $A$ be a central simple $K$-algebra split by $E$, where $E supset K$, and
  where
  $
    (A : K) = (E : K)^2.
  $
  Then $E$ can be embedded in $A$ as a self-centralizing maximal subfield of
  $A$.
] <cor:self-centralizing-embedding>

#proof[
  Let $D$ be the skewfield part of $A$, so $E$ splits $D$, and let
  $E subset M_r (D) = B$ with $r$ minimal, as in
  @th:splitting-field-matrix-embedding. By
  @rem:self-centralizing-maximal-subfield we have
  $
    (B : K) = (E : K)^2 = (A : K),
  $
  whence $A tilde.equiv B$. The desired result is now obvious, since $E$ is a
  self-centralizing maximal subfield of $B$.
]

#corollary[
  For each central simple $K$-algebra $A'$, there exists a finite galois
  extension $L$ of $K$ which splits $A'$. Further, $A' tilde.op A$ for some
  central simple $K$-algebra $A$ containing $L$ as a self-centralizing maximal
  subfield. Finally,
  $
    B(K) = union.big B(L slash K),
  $ <eq:brauer-group-union>
  where $L$ ranges over all finite galois extensions of $K$.
] <cor:galois-splitting-field>

#proof[
  Given $A'$, by @th:maximal-subfields there exists a finite separable extension
  $E$ of $K$ such that $E$ splits $A'$. Let $L$ be the normal closure of $E$
  over $K$, that is, the #source(250)smallest galois extension of $K$ containing
  $E$. Then $L$ is also a splitting field for $A'$, and $L$ is a finite galois
  extension of $K$.

  The above shows that $[A'] in B(L slash K)$, which implies at once that
  @eq:brauer-group-union holds true.

  Finally, if $D$ is the skewfield part of $A'$, then $L$ splits $D$. As in
  @th:splitting-field-matrix-embedding, let $L subset M_r (D)$ be an embedding
  with minimal $r$, and set $A = M_r (D)$. By
  @rem:self-centralizing-maximal-subfield, $L$ is a self-centralizing maximal
  subfield of $A$. Clearly $A' tilde.op A$, and the proof is complete.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $D$ be a skewfield with center $K$, index $m$. Let $E$ be a finite
  extension of $K$ which splits $D$. Then the least value of $r$ for which there
  is an embedding of $K$-algebras $E subset M_r (D)$ is given by
  $r = (E : K) slash m$.
] <exc:minimal-embedding-degree>

#exercise[
  Let $K$ be a field. Show that the set of conjugacy classes of subfields of
  $M_r (K)$ which contain the center $K$ of $M_r (K)$ is in one-to-one
  correspondence with the set of isomorphism classes of extension fields $E$ of
  $K$ for which $(E : K)$ divides $r$. What are the maximal subfields of
  $M_r (K)$ containing $K$? Show that such maximal subfields are not necessarily
  self-centralizing.
] <exc:subfields-of-matrix-algebra>

#exercise[
  Let $A$ and $B$ be $K$-algebras, and let $M$ be simultaneously a right
  $A$-module and a right $B$-module. We wish to make $M$ into a right
  $A times.o_K B$-module, by defining
  $
    m(a times.o b) = m a b, quad a in A, quad b in B, quad m in M.
  $
  Show that this procedure is justified if and only if $A subset Hom_B (M, M)$.
] <exc:tensor-product-module>
