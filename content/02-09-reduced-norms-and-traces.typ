#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/02-09-reduced-norms-and-traces.typ": conjugate-splitting

== Reduced norms and traces <sec:reduced-norms-and-traces>

=== Central simple algebras <ss:central-simple-algebras>

Throughout this subsection, let $A$ denote a central simple $K$-algebra, that
is, a simple $K$-algebra with center $K$, such that $(A : K)$ is finite. We have
seen in §~@ss:min-char-pol how to assign to each $a in A$ a characteristic
polynomial, norm and trace, as follows: let $a_L in Hom_K (A, A)$ be left
multiplication by $a$ on $A$, and set
$
  charpol_(A slash K) a & = "char. pol. of" a_L \
  & = X^m - (T_(A slash K) a) X^(m-1) + dots.c + (-1)^m N_(A slash K) a,
$
where $m = (A : K)$. Here $T = T_(A slash K)$ is the _trace_ map, and
$N = N_(A slash K)$ the _norm_ map. For any $X, Y in M_m (K)$ we know that
$"trace"(X Y) = "trace"(Y X)$. Therefore
$
  cases(
    T(a b) = T(b a)"," T(a + b) = T(a) + T(b)"," T(r a) = r T(a)",",
    N(a b) = N(a) N(b)"," N(r a) = r^m N(a)",",
  )
$ <eq:algebra-trace-norm>
for $a, b in A$, $r in K$.

#source(122)The above definitions make no use of the assumption that $A$ is a
central simple algebra. For central simple algebras, it is possible to introduce
more useful concepts, namely those of reduced characteristic polynomial, reduced
norm and reduced trace. We proceed to show how this may be done.

Since $A$ is a simple algebra with center $K$, there exists by
§~@ss:splitting-fields an extension field $E$ of $K$ which splits $A$. This
means that there is an isomorphism of $E$-algebras
$
  h : E times.o_K A tilde.equiv M_n (E), quad "where" quad (A : K) = n^2.
$ <eq:splitting-isomorphism>
If $g$ is another such isomorphism, then $h dot g^(-1)$ is an $E$-automorphism
of $M_n (E)$. Each such automorphism is inner, by @cor:automorphisms-inner, and
so there exists an invertible $t in M_n (E)$ such that
$
  h(u) = t dot g(u) dot t^(-1), quad u in E times.o_K A.
$
Consequently the matrices $g(u)$ and $h(u)$ have the same characteristic
polynomial. This shows that $charpol h(u)$ does not depend on the choice of the
$E$-isomorphism $h$ in @eq:splitting-isomorphism.

For $a in A$, define its _reduced characteristic polynomial_ as
#idx("reduced characteristic polynomial")
#idx("characteristic polynomial (reduced)")
$
  redcharpol_(A slash K) a = charpol h(1 times.o a).
$
We shall omit the subscript $A slash K$ when there is no danger of confusion.

#theorem[
  For each $a in A$, $redcharpol_(A slash K) a$ lies in $K[X]$, and is
  independent of the choice of the splitting field $E$ of $A$ used to define
  $redcharpol$
] <th:reduced-char-pol-rational>

#proof[
  Let us show first that if $F supset K$ is another splitting field for $A$,
  then $redcharpol$ obtained using $F$ is the same as that obtained by using
  $E$. By Exercise~@exc:common-extension-field, there exist $K$-embeddings
  $E -> Omega$, $F -> Omega$, where $Omega$ is some field containing $K$. It
  suffices to prove that $redcharpol$ via $E$ is the same as $redcharpol$ via
  $Omega$. We have an $Omega$-algebra isomorphism
  $
    1 times.o h : Omega times.o_E (E times.o_K A) tilde.equiv
    Omega times.o_E M_n (E).
  $
  After canonical identifications, we may rewrite the above $Omega$-isomorphism
  as (say)
  $
    h' : Omega times.o_K A tilde.equiv M_n (Omega),
  $
  so $Omega$ is also a splitting field for $A$. Any element $u in E times.o_K A$
  may also be viewed as element of $Omega times.o_K A$. When this is done,
  $h'(u)$ is precisely the matrix $h(u)$ #source(123)viewed as element of
  $M_n (Omega)$. Consequently
  $
    charpol h(u) = charpol h'(u), quad u in E times.o_K A.
  $
  This holds in particular when $u = 1 times.o a$, $a in A$, and so
  $redcharpol_(A slash K) a$ is the same when computed via $E$ as via $Omega$.
  This completes the proof that $redcharpol$ does not depend on the choice of
  splitting field.

  In order to prove that $redcharpol a in K[X]$ for $a in A$, we observe that by
  @th:maximal-subfields we may find a finite separable extension $E$ of $K$
  which splits $A$. Since any extension field of $E$ also splits $A$, we may in
  fact take $E$ to be a finite galois extension of $K$. Let $G$ be the galois
  group of $E$ over $K$; then each $sigma in G$ is a $K$-automorphism of $E$,
  and $K$ is the subfield of $E$ fixed by $G$. To clarify the following
  argument, we start with any $K$-isomorphism $f : E tilde.equiv E'$ of fields
  containing $K$, and later on we will choose $E' = E$, and $f = sigma in G$.

  Consider the diagram
  $
    #conjugate-splitting
  $
  Here, $h$ is the $E$-isomorphism in @eq:splitting-isomorphism, and $f^*$ takes
  a matrix in $M_n (E)$ onto a matrix in $M_n (E')$ by applying $f$ to each of
  its entries. The map $h'$ is then defined by requiring the diagram to be
  commutative. Then $h'$ is an isomorphism of $E'$-algebras, since $h$ is an
  $E$-isomorphism. Hence for $a in A$,
  $
    f^* {h(1 times.o a)} = {h' (f times.o 1)} (1 times.o a)
    = h'(1 times.o a).
  $
  Therefore
  $
    redcharpol a " (via" E') & = charpol h'(1 times.o a) \
                             & = charpol f^* {h(1 times.o a)} \
                             & = f{charpol h(1 times.o a)} \
                             & = f{redcharpol a " (via" E)},
  $
  where $f$ is applied to a polynomial in $E[X]$ by acting on each of its
  coefficients.

  Now let $E' = E$, and let $f$ range over all elements of $G$. Then the above
  shows that for $a in A$, each coefficient in $redcharpol a$ is fixed by $f$.
  Therefore each coefficient lies in $K$, and so $redcharpol a in K[X]$, as
  claimed. This completes the proof.
]

#example[
  Let $A = bold(Q) plus.o bold(Q) i plus.o bold(Q) j plus.o bold(Q) k$ be the
  skewfield of quaternions over $bold(Q)$, where #idx("quaternion skewfield")
  $
    i^2 = j^2 = -1, quad k = i j = -j i.
  $
  #source(124)Clearly $A$ has center $bold(Q)$, and $E = bold(Q)(i)$ is a
  maximal subfield of $A$, hence is a splitting field for $A$. Each $a in A$ is
  uniquely expressible as
  $
    a = alpha + beta j, quad alpha, beta in E.
  $
  There is an $E$-isomorphism
  $
    h : E times.o_bold(Q) A tilde.equiv M_2 (E),
  $
  given by
  $
    1 times.o alpha -> mat(alpha, 0; 0, overline(alpha)), quad
    1 times.o beta j -> mat(0, beta; -overline(beta), 0),
  $
  where bars denote complex conjugation. Therefore
  $
    redcharpol_(A slash bold(Q)) a
    & = charpol mat(alpha, beta; -overline(beta), overline(alpha)) \
    & = det mat(X - alpha, -beta; overline(beta), X - overline(alpha)) \
    & = X^2 - (alpha + overline(alpha)) X
    + (alpha overline(alpha) + beta overline(beta)) in bold(Q)[X].
  $
  Hence (see @eq:reduced-trace-norm below)
  $
    tr_(A slash bold(Q)) a = alpha + overline(alpha), quad
    nr_(A slash bold(Q)) a = alpha overline(alpha) + beta overline(beta).
  $
] <exm:quaternions>

Returning to the general case, we have

#theorem[
  If $(A : K) = n^2$, then
  $
    charpol_(A slash K) a = {redcharpol_(A slash K) a}^n, quad a in A.
  $
] <th:char-pol-power-of-reduced>

#proof[
  Let $E supset K$ split $A$, so $E times.o_K A tilde.equiv M_n (E)$. By
  Exercise~@exc:char-pol-ground-field,
  $
    charpol_(A slash K) a = charpol_(E times.o A slash E) 1 times.o a, quad
    a in A,
  $
  where $times.o$ denotes $times.o_K$. By @th:matrix-ring-simple there is a left
  $E times.o A$-isomorphism $E times.o A tilde.equiv V^((n))$, where $V$ is a
  minimal left ideal of $E times.o A$. Hence
  $
    charpol_(E times.o A slash E) 1 times.o a = f(X)^n,
  $
  where $f(X)$ is the characteristic polynomial of the matrix $(1 times.o a)_L$
  which describes the action of $1 times.o a$ on some $E$-basis of $V$. On the
  other hand, the $E$-isomorphism in @eq:splitting-isomorphism can be obtained
  by mapping each $y in E times.o A$ onto the matrix $y_L$ giving the action of
  $y$ on some $E$-basis of $V$, and thus
  $
    charpol h(y) = charpol y_L, quad y in E times.o A.
  $
  Taking $y = 1 times.o a$ with $a in A$, we obtain
  #source(125)
  $
    redcharpol_(A slash K) a & = charpol h(1 times.o a) \
                             & = charpol (1 times.o a)_L.
  $ <eq:reduced-char-pol-left-ideal>
  Hence $charpol_(A slash K) a = f(X)^n$, as desired.
]

Let us write #display-variant(
  [@eq:reduced-char-pol-left-ideal],
  $
    redcharpol_(A slash K) a = X^n - (tr a) X^(n-1) + dots.c
    + (-1)^n nr(a), a in A.
  $,
) <eq:reduced-trace-norm>
We call $tr(a)$ the _reduced trace_ of $a$, and $nr(a)$ the _reduced norm_ of
$a$. It follows at once from @th:char-pol-power-of-reduced that #idx(
  "reduced trace",
)#idx("trace (reduced)") #idx("reduced norm")#idx("norm (reduced)")
$
  T_(A slash K) a = n dot tr(a), quad N_(A slash K) a = (nr(a))^n.
$ <eq:trace-norm-reduced-powers>
Furthermore, using the notation of @eq:reduced-char-pol-left-ideal, the map
$a -> (1 times.o a)_L$, $a in A$, gives a $K$-algebra isomorphism of $A$ into
$Hom_E (V, V)$. Since
$
  tr(a) = "trace of" (1 times.o a)_L, quad
  nr(a) = "determinant of" (1 times.o a)_L,
$
we conclude that
$
  cases(
    tr(a b) & = tr(b a)"," quad tr(a + b) = tr(a) + tr(b)"," quad
              tr(s a) = s dot tr(a)",",
    nr(a b) & = nr(a) dot nr(b)"," quad nr(s a) = s^n dot nr(a)",",
  )
$ <eq:reduced-trace-norm-properties>
for $a, b in A$, $s in K$.

#theorem[
  The reduced trace map gives rise to a symmetric nondegenerate $K$-bilinear
  form $tau : A times A -> K$, by setting
  $
    tau(a, b) = tr(a b), quad a, b in A.
  $
  Further, $tau$ is _associative_, that is,
  #idx("associative bilinear form")
  $
    tau(a b, c) = tau(a, b c) "for" a, b, c in A.
  $
] <th:reduced-trace-form>

#proof[
  It is clear that $tau$ is symmetric and associative, and we need only prove
  that $tau$ is nondegenerate. Let $E supset K$ split $A$, so
  $E times.o_K A tilde.equiv M_n (E)$. We may extend $tau$ to an $E$-bilinear
  map
  $
    tau' : (E times.o A) times (E times.o A) -> E,
  $
  and indeed from the definition of reduced trace, we have
  $
    tau'(u, v) = "trace"(u v), quad u, v in E times.o A tilde.equiv M_n (E),
  $
  where $"trace"(u v)$ is the ordinary trace of the matrix $u v$. Furthermore,
  $tau$ is nondegenerate if and only if $tau'$ is nondegenerate.

  Let
  $
    B = {u in M_n (E) : "trace"(u v) = 0 "for all" v in M_n (E)}.
  $
  #source(126)Since $tau'$ is symmetric, $B$ is a two-sided ideal in the ring
  $M_n (E)$. But $B$ does not contain the identity matrix $I_n$, and thus
  $B = 0$. Hence $tau'$ is nondegenerate, whence so is $tau$. This completes the
  proof.
]

If $op("char") K$ divides $n$, it follows from @eq:trace-norm-reduced-powers
that the ordinary trace map $T_(A slash K)$ is the zero map. Hence in this case
it is essential to use the reduced trace, rather than the ordinary trace, in
@th:reduced-trace-form[Theorem] and its applications.

=== Semisimple algebras <ss:reduced-norms-semisimple>

In the preceding subsection we have defined the reduced characteristic
polynomial, reduced norm and reduced trace, for elements of a central simple
$K$-algebra $A$. The aim of this subsection is to generalize these concepts to
the case where $A$ is an arbitrary finite dimensional semisimple $K$-algebra.

We begin the discussion with some elementary results from linear algebra. Let
$K subset L$ be fields, with $(L : K) = n$. Each $alpha in L$ maps onto a matrix
$tilde(alpha) in M_n (K)$ describing the action of left multiplication by
$alpha$ on some $K$-basis of $L$. Given
$
  f(X) = sum alpha_i X^i in L[X],
$
define
$
  tilde(f)(X) = sum tilde(alpha)_i X^i in M_n (K[X]).
$
We now define a _norm_ map $N_(L slash K) : L[X] -> K[X]$ by setting
$
  N_(L slash K) f(X) = det tilde(f)(X), quad f(X) in L[X].
$
Let us establish some basic properties of this norm:

#theorem[
  Let $K subset L$ be fields, with $(L : K) = n$. Then
  + $N_(L slash K)$ is multiplicative.
  + For $alpha_1, dots, alpha_s in L$, we have
    $
      N_(L slash K) & (X^s + alpha_1 X^(s-1) + dots.c + alpha_s) \
                    & = X^(n s) + (T_(L slash K) alpha_1) X^(n s - 1)
                      + dots.c + N_(L slash K) alpha_s.
    $ <eq:polynomial-norm-coefficients>
  + Let $V$ be an $s$-dimensional $L$-space, and let $phi$ be an
    $L$-endomorphism of $V$. We may view $phi$ as a $K$-endomorphism of $V$.
    Then
    $
      charpol_(V slash K) phi = N_(L slash K) (charpol_(V slash L) phi).
    $ <eq:char-pol-restriction-of-scalars>
] <th:polynomial-norm>

#proof[
  Write $N$ in place of $N_(L slash K)$, and let $f, g in L[X]$. The map
  $alpha -> tilde(alpha)$, $alpha in L$, is a ring homomorphism. Therefore
  $tilde(f g) = tilde(f) tilde(g)$, and so
  $
    N(f g) = det(tilde(f g)) = (det tilde(f))(det tilde(g)) = (N f)(N g).
  $
  #source(127)This establishes (i).

  Next we have
  $
    N(X^s + alpha_1 X^(s-1) + dots.c + alpha_s)
    & = det(tilde(1) X^s + tilde(alpha)_1 X^(s-1) + dots.c + tilde(alpha)_s) \
    & = X^(n s) + (tr tilde(alpha)_1) X^(n s - 1) + dots.c
    + det tilde(alpha)_s,
  $
  with the second equality following from an obvious calculation. This yields
  assertion (ii), since by §~@sec:integral-closure we have
  $
    tr tilde(alpha)_1 = T_(L slash K) alpha_1, quad
    det tilde(alpha)_s = N_(L slash K) alpha_s.
  $

  To prove (iii), we first write $V = dsum V_i$ where each $V_i$ is an
  $L$-subspace of $V$ such that $phi(V_i) subset V_i$. Then
  $
    charpol_(V slash K) phi = product_i charpol_(V_i slash K) phi,
  $
  and likewise with $K$ replaced by $L$. In view of assertion (i), it therefore
  suffices to establish @eq:char-pol-restriction-of-scalars for each $V_i$.
  Changing notation, we may hereafter assume that $V$ is an indecomposable
  $L[phi]$-module. Thus we may write
  $
    V = L[X] slash (f(X)) "for some" f(X) in L[X],
  $
  with $phi$ acting on $V$ as left multiplication by $X$. Then
  $
    charpol_(V slash L) phi = f(X)
    = X^s + alpha_1 X^(s-1) + dots.c + alpha_s "(say)".
  $

  Now let $L = dsum_(j=1)^n K u_j$, and let us calculate the action of $phi$ on
  the $K$-basis of $V$ consisting of the elements
  ${u_j X^i : 1 <= j <= n, 0 <= i <= s - 1}$. Relative to a suitable indexing of
  these basis elements, the action of $phi$ is given by the matrix
  $
    mu = mat(
      delim: "[",
      0, 0, dots, 0, -tilde(alpha)_s;
      I, 0, dots, 0, -tilde(alpha)_(s-1);
      0, I, dots, 0, -tilde(alpha)_(s-2);
      dots, dots, dots, dots, dots;
      0, 0, dots, I, -tilde(alpha)_1;
    ).
  $
  This matrix $mu$ is an $s times s$ array of blocks, each of size $n times n$.
  We have
  $
    charpol_(V slash K) phi = det(X I - mu) = mat(
      delim: "|",
      X tilde(1), tilde(0), dots, tilde(0), tilde(alpha)_s;
      -tilde(1), X tilde(1), dots, tilde(0), tilde(alpha)_(s-1);
      dots, dots, dots, dots, dots;
      tilde(0), tilde(0), dots, X tilde(1), tilde(alpha)_2;
      tilde(0), tilde(0), dots, -tilde(1), X tilde(1) + tilde(alpha)_1;
    ).
  $
  #source(128)Now perform elementary row operations on this determinant, from
  the bottom up: add $X$ times the $s$th row of blocks to the $(s - 1)$th row,
  then $X$ times the $(s - 1)$th row of blocks to the $(s - 2)$th row, and so
  on. This gives
  $
    charpol_(V slash K) phi & = mat(
                                delim: "|",
                                tilde(0), tilde(0), dots, tilde(0), tilde(f)(X);
                                -tilde(1), tilde(0), dots, tilde(0), *;
                                dots, dots, dots, dots, dots;
                                tilde(0), tilde(0), dots, tilde(0), *;
                                tilde(0), tilde(0), dots, -tilde(1), *;
                              ) \
                            & = det tilde(f)(X) = N_(L slash K) f(X).
  $
  This completes the proof of (iii), and establishes the theorem.
]

Any semisimple $K$-algebra $A$ may be written as a direct sum $dsum A_i$ of
simple algebras $A_i$, whose centers are finite extensions of $K$. In order to
define $redcharpol_(A slash K) a$ for each $a in A$, we shall first treat the
case in which $A$ is a simple $K$-algebra; the extension to the semisimple case
will be straightforward.

#definition[
  Let $B$ denote a central simple $L$-algebra with $(B : L) = m^2$, and let $K$
  be a subfield of $L$ with $(L : K) = n$. For each $b in B$, we define its
  _reduced characteristic polynomial relative to $K$_ by
  #idx("reduced characteristic polynomial")
  #idx("characteristic polynomial (reduced)")
  $
    redcharpol_(B slash K) b & = N_(L slash K) (redcharpol_(B slash L) b) \
                             & = X^(m n) - (tr_(B slash K) b) X^(m n - 1)
                               + dots.c + (-1)^(m n) nr_(B slash K) b.
  $
  We call $tr_(B slash K)$ the _relative reduced trace_, and $nr_(B slash K)$
  the _relative reduced norm_. When $L = K$, the preceding concepts reduce to
  those given in §~@ss:central-simple-algebras. #idx("reduced trace")#idx(
    "trace (reduced)",
  ) #idx("reduced norm")#idx("norm (reduced)")
] <def:relative-reduced-char-pol>

Before proceeding to the case of semisimple $K$-algebras, let us establish some
basic properties of relative reduced traces, norms, and characteristic
polynomials.

#theorem[
  Let $B$ be a central simple $L$-algebra, $K$ a subfield of $L$, and let
  $(B : L) = m^2$, $(L : K) = n$. For each $b in B$, we have
  $
    tr_(B slash K) b = T_(L slash K) (tr_(B slash L) b), quad
    nr_(B slash K) b = N_(L slash K) (nr_(B slash L) b),
  $ <eq:relative-trace-norm-transitivity>
  $
    charpol_(B slash K) b = {redcharpol_(B slash K) b}^m,
  $ <eq:relative-char-pol-power>
  $
    T_(B slash K) b = m dot tr_(B slash K) b, quad
    N_(B slash K) b = {nr_(B slash K) b}^m.
  $ <eq:relative-trace-norm-powers>
] <th:relative-reduced-properties>

#proof[
  Given $b in B$, let us set
  $
    h(X) = redcharpol_(B slash L) b
    = X^m - alpha_1 X^(m-1) + dots.c + (-1)^m alpha_m.
  $
  #source(129)Then $alpha_1 = tr_(B slash L) b$, $alpha_m = nr_(B slash L) b$,
  according to the definitions in §~@ss:central-simple-algebras. But therefore
  $
    redcharpol_(B slash K) b & = N_(L slash K) h(X) \
                             & = X^(m n) - (T_(L slash K) alpha_1) X^(m n - 1)
                               + dots.c + (-1)^(m n) N_(L slash K) alpha_m,
  $
  by @eq:polynomial-norm-coefficients. Comparing this expression with that given
  in @def:relative-reduced-char-pol, we conclude at once that
  $
    tr_(B slash K) b = T_(L slash K) alpha_1, quad
    nr_(B slash K) b = N_(L slash K) alpha_m.
  $
  This yields the desired formulas @eq:relative-trace-norm-transitivity.

  Next, we may compute $charpol_(B slash K) b$ by considering the left
  multiplication by the element $b$ acting on a $K$-basis for $B$; a
  corresponding statement holds with $K$ replaced by $L$. Therefore
  $
    charpol_(B slash K) b & = N_(L slash K) (charpol_(B slash L) b) quad
                            "by" #[@eq:char-pol-restriction-of-scalars] \
                          & = N_(L slash K) {(redcharpol_(B slash L) b)^m} quad
                            "by" #[@th:char-pol-power-of-reduced] \
                          & = {N_(L slash K) (redcharpol_(B slash L) b)}^m quad
                            "by" #[@th:polynomial-norm] \
                          & = {redcharpol_(B slash K) b}^m.
  $
  This proves @eq:relative-char-pol-power; since @eq:relative-trace-norm-powers
  is an obvious consequence of @eq:relative-char-pol-power, the theorem is
  established.
]

#corollary[
  The analogues of formulas @eq:reduced-trace-norm-properties hold for
  $tr_(B slash K)$ and $nr_(B slash K)$.
] <cor:relative-reduced-trace-norm-properties>

#proof[
  The assertion is clear from @eq:reduced-trace-norm-properties and
  @eq:relative-trace-norm-transitivity. We remark merely that
  $
    nr_(B slash K) alpha b = alpha^(m n) dot nr_(B slash K) b, quad
    alpha in K, quad b in B.
  $
]

We are now ready to generalize @th:reduced-trace-form[Theorem], as follows:

#theorem[
  Let $B$ be a simple $K$-algebra whose center $L$ is separable over $K$. Then
  the map $tr_(B slash K)$ gives rise to a symmetric associative nondegenerate
  bilinear form from $B times B$ to $K$.
] <th:relative-reduced-trace-form>

#proof[
  The form is given by $tau(a, b) = tr_(B slash K) (a b)$, $a, b in B$, and we
  need only check that $tau$ is nondegenerate. If $tau(a, b) = 0$ for all
  $b in B$, then
  $
    T_(L slash K) (alpha dot tr_(B slash L) (a b))
    = T_(L slash K) (tr_(B slash L) (alpha dot a b)) = 0
    "for all" alpha in L, quad b in B.
  $
  But $T_(L slash K)$ gives a nondegenerate trace form, since $L$ is separable
  over $K$, and #source(130)hence we have $tr_(B slash L) a b = 0$ for all
  $b in B$. Therefore $a = 0$ by @th:reduced-trace-form, which completes the
  proof.
]

(We remark that the existence of a symmetric associative nondegenerate bilinear
form on $B$ to $K$ tells us that $B$ is a Frobenius algebra over $K$ (see
Curtis–Reiner [@bib:Curtis1962, (61.3)]); we know this anyway, since every
simple $K$-algebra is a Frobenius algebra. The significance of
@th:relative-reduced-trace-form lies in the fact that the form arises from the
reduced trace map $tr_(B slash K)$.)

Suppose now that $A$ is any semisimple $K$-algebra, and write
$
    A & = A_1 plus.o dots.c plus.o A_t "(simple components)", \
  K_i & = "center of" A_i, quad (A_i : K_i) = m_i^2, quad 1 <= i <= t.
$
Each $K_i$ is a finite extension field of $K$. Every element $a in A$ is
uniquely expressible as $a = a_1 + dots.c + a_t$, $a_i in A_i$. We define
#idx("reduced characteristic polynomial")
#idx("characteristic polynomial (reduced)")
$
  redcharpol_(A slash K) a & = product_(i=1)^t redcharpol_(A_i slash K) a_i \
  & = product_(i=1)^t N_(K_i slash K) (redcharpol_(A_i slash K_i) a_i).
$ <eq:semisimple-reduced-char-pol>
As usual, we define $tr_(A slash K)$ and $nr_(A slash K)$ by the equation #idx(
  "reduced trace",
)#idx("trace (reduced)") #idx("reduced norm")#idx("norm (reduced)")
$
  redcharpol_(A slash K) a = X^r - (tr_(A slash K) a) X^(r-1) + dots.c
  + (-1)^r nr_(A slash K) a
$ <eq:semisimple-reduced-trace-norm>
for each $a in A$, where $r = sum m_i (K_i : K)$. For future use, we record the
following obvious consequences of these definitions:
$
  tr_(A slash K) a = sum_(i=1)^t tr_(A_i slash K) a_i
  = sum_(i=1)^t T_(K_i slash K) (tr_(A_i slash K_i) a_i),
$ <eq:semisimple-reduced-trace>
$
  nr_(A slash K) a = product_(i=1)^t nr_(A_i slash K) a_i
  = product_(i=1)^t N_(K_i slash K) (nr_(A_i slash K_i) a_i).
$ <eq:semisimple-reduced-norm>
From @eq:relative-char-pol-power, we also obtain
$
  charpol_(A slash K) a = product_(i=1)^t charpol_(A_i slash K) a_i
  = product_(i=1)^t {redcharpol_(A_i slash K) a_i}^(m_i),
$ <eq:semisimple-char-pol>
$
  T_(A slash K) a = sum_(i=1)^t m_i tr_(A_i slash K) a_i, quad
  N_(A slash K) a = product_(i=1)^t {nr_(A_i slash K) a_i}^(m_i).
$ <eq:semisimple-trace-norm>
Of course, the analogues of formulas @eq:reduced-trace-norm-properties remain
true for $tr_(A slash K)$ and $nr_(A slash K)$.

From @th:relative-reduced-trace-form we have at once

#theorem[
  Let $A$ be a separable $K$-algebra. Then the map $tr_(A slash K)$ gives rise
  to a symmetric associative nondegenerate bilinear trace form from $A times A$
  to $K$.
] <th:separable-reduced-trace-form>

#source(131)Finally, we show that reduced characteristic polynomials, norms and
traces, are not affected by change of ground field. We prove

#theorem[
  Let $A$ be a separable $K$-algebra, and let $F$ be any field containing $K$
  (not necessarily finite dimensional over $K$). View $A$ as embedded in the
  separable $F$-algebra $F times.o A$, where $times.o$ means $times.o_K$. Then
  for all $a in A$,
  $
    redcharpol_(F times.o A slash F) a = redcharpol_(A slash K) a,
  $ <eq:reduced-char-pol-ground-field>
  $
    tr_(F times.o A slash F) a = tr_(A slash K) a, quad
    nr_(F times.o A slash F) a = nr_(A slash K) a.
  $ <eq:reduced-trace-norm-ground-field>
] <th:reduced-ground-field>

#proof[
  By Exercise~@exc:separable-base-change, $F times.o A$ is a separable
  $F$-algebra. We have
  $
    charpol_(F times.o A slash F) a = charpol_(A slash K) a
  $ <eq:char-pol-ground-field>
  by Exercise~@exc:char-pol-ground-field, a fact which we shall use presently.
  It suffices to prove the theorem for the case where $A$ is a central simple
  $L$-algebra, with $L$ a finite separable extension of $K$. By
  Exercise~@exc:separable-extension-decomposition, we may write
  $
    F times.o A tilde.equiv dsum_(j=1)^d B_j, quad B_j = F_j times.o_L A,
  $
  where each $F_j$ is a field containing $L$ and $F$. Here, each $B_j$ is a
  central simple $F_j$-algebra, and $(B_j : F_j) = (A : L) = m^2$, say. For
  $a in A$, write $a = b_1 + dots.c + b_d$, $b_j in B_j$. Then
  @eq:semisimple-char-pol yields
  $
    charpol_(F times.o A slash F) a
    & = product_(j=1)^d {redcharpol_(B_j slash F) b_j}^m \
    & = {redcharpol_(F times.o A slash F) a}^m.
  $
  Since
  $
    charpol_(A slash K) a = {redcharpol_(A slash K) a}^m
  $
  by @eq:relative-char-pol-power, we now deduce
  @eq:reduced-char-pol-ground-field as a direct consequence of
  @eq:char-pol-ground-field. The formulas in @eq:reduced-trace-norm-ground-field
  follow from @eq:reduced-char-pol-ground-field, and the theorem is proved.
]

For each element $a$ of a $K$-algebra $A$, we have computed
$charpol_(A slash K) a$ by letting $a$ act from the left on a $K$-basis of $A$.
We shall conclude this section by showing that when $A$ is a separable
$K$-algebra, we could equally well have calculated the characteristic polynomial
of $a$ by letting $a$ act from the right. For each $a in A$, we defined
$
  a_L : x -> a x, quad x in A, quad a_R : x -> x a, quad x in A,
$
so $a_L$ and $a_R$ are a pair of $K$-linear transformations on $A$. In
§~@sec:integral-closure we defined
$
  charpol_(A slash K) a = charpol_K a_L.
$
We now prove

#theorem[
  #source(132)Let $A$ be a separable $K$-algebra. Then
  $
    charpol_K a_L = charpol_K a_R
  $
  for each $a in A$.
] <th:left-right-char-pol>

#proof[
  Let $A = dsum_(i=1)^n K x_i$, and let ${y_1, dots, y_n}$ be a dual basis of
  $A$ relative to the reduced trace form, so
  $
    A = dsum_(j=1)^n K y_j, quad tr x_i y_j = delta_(i j), quad
    1 <= i, j <= n,
  $
  where $tr$ is an abbreviation for $tr_(A slash K)$. We shall compute
  $charpol_K a_L$ by letting $a_L$ act on the $K$-basis ${x_i}$, and we shall
  compute $charpol_K a_R$ by letting $a_R$ act on the $K$-basis ${y_j}$. For
  $1 <= j <= n$, let
  $
    a_L (x_j) = a x_j = sum_i alpha_(i j) x_i, quad
    a_R (y_j) = y_j a = sum_i beta_(i j) y_i,
  $
  where the $alpha_(i j), beta_(i j) in K$. Then
  $
    charpol_K a_L = det(X delta_(i j) - alpha_(i j)), quad
    charpol_K a_R = det(X delta_(i j) - beta_(i j)).
  $
  However, for each $i, j$ we have
  $
    alpha_(i j) = tr y_i a x_j, quad beta_(i j) = tr y_j a x_i.
  $
  Thus the matrices $(alpha_(i j))$ and $(beta_(i j))$ are transposes of one
  another, and hence have the same characteristic polynomial. This completes the
  proof of the theorem.
]

#corollary[
  Let $A = dsum K x_i$, and let
  $
    x_j a = sum gamma_(i j) x_i, quad gamma_(i j) in K.
  $
  Then
  $
    N_(A slash K) a = det(gamma_(i j)), quad
    T_(A slash K) a = "trace of" (gamma_(i j)).
  $
] <cor:right-norm-trace>

It should be pointed out that @th:left-right-char-pol and @cor:right-norm-trace
need not be true for arbitrary finite dimensional $K$-algebras $A$. The
following example is given in Bourbaki [@bib:Bourbaki1958, §~12, no.~3]: let
$A = K plus.o K x plus.o K y$, where
$
  x^2 = x, quad x y = y, quad y x = 0, quad y^2 = 0.
$
Relative to the basis ${1, x, y}$, we have
$
  x_L = mat(0, 0, 0; 1, 1, 0; 0, 0, 1), quad
  x_R = mat(0, 0, 0; 1, 1, 0; 0, 0, 0),
$
#source(133)and $x_L$, $x_R$ have different characteristic polynomials.
Furthermore, $x_L$ and $x_R$ have different traces, and if $op("char") K != 2$,
then $(1 + x)_L$ and $(1 + x)_R$ have different determinants.

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $A$ be a central simple $K$-algebra, and let $E$ be a subfield of $A$ such
  that $(A : K) = (E : K)^2$. Show that for every $a in E$,
  $
    redcharpol_(A slash K) a = (minpol_K a)^((E : K(a))).
  $
  #hint[@exc:reduced-char-pol-maximal-subfield][Let $f(X) = minpol_K a$; then
    $f(X)$ has degree $(K(a) : K)$. But $redcharpol_(A slash K) a$ is a power of
    $f(X)$, and has degree $(E : K)$.]
  <hint:reduced-char-pol-maximal-subfield>
] <exc:reduced-char-pol-maximal-subfield>

#exercise[
  Let $A$ be a central simple $K$-algebra, where $K$ is any perfect field (that
  is, $K$ has no inseparable extensions). Using @th:char-pol-power-of-reduced,
  prove directly that $redcharpol_(A slash K) a in K[X]$ for each $a in A$.
  #hint[@exc:reduced-char-pol-perfect-field][Show that if $E$ is an extension
    field of $K$, and $f(X) in E[X]$ is such that $f(X)^n in K[X]$, then also
    $f(X) in K[X]$.] <hint:reduced-char-pol-perfect-field>
] <exc:reduced-char-pol-perfect-field>

#exercise[
  Let $A$ be a separable $K$-algebra, and choose a field $E supset K$ such that
  $
    E times.o_K A = dsum_(j=1)^d B_j, quad
    "where" phi_j : B_j tilde.equiv M_(n_j) (E), quad 1 <= j <= d.
  $
  Let $pi_j : E times.o_K A -> B_j$. Prove that for every $a in A$,
  $
    redcharpol_(A slash K) a
    = product_(j=1)^d charpol phi_j pi_j (1 times.o a).
  $ <eq:reduced-char-pol-components>
  #hint[@exc:reduced-char-pol-components][Let $f(X)$ denote the expression on
    the right hand side of @eq:reduced-char-pol-components. As in the proof of
    @th:reduced-char-pol-rational, the isomorphism $phi_j$ is unique up to an
    inner automorphism of $M_(n_j) (E)$, and hence $f(X)$ does not depend on the
    choice of the maps ${phi_j}$. The proof of @th:reduced-char-pol-rational
    carries over to this case, and shows that $f(X)$ does not depend on the
    choice of $E$, and that $f(X) in K[X]$.

    To prove @eq:reduced-char-pol-components, it suffices to treat the case
    where $A$ is a central simple $L$-algebra, with $L slash K$ separable.
    Choose $E supset L$ so that
    $
      E times.o_L A tilde.equiv M_m (E), quad "where" quad (A : L) = m^2,
    $
    and so that
    $
      E times.o_K L tilde.equiv dsum_(i=1)^n E_i, quad "where" quad
      (L : K) = n,
    $
    and where each $E_i$ equals $E$ and contains an isomorphic copy of $L$. Then
    $
      E times.o_K A tilde.equiv (E times.o_K L) times.o_L A
      tilde.equiv dsum_(i=1)^n E_i times.o_L A = dsum_(i=1)^n M_m (E_i).
    $
    #source(134)But then by @eq:reduced-char-pol-ground-field
    $
      redcharpol_(A slash K) a
      & = redcharpol_(E times.o_K A slash E) 1 times.o a \
      & = product_(i=1)^n charpol (psi_i (1 times.o a)) = f(X),
    $
    where $psi_i : E times.o_K A -> M_m (E_i)$.]
  <hint:reduced-char-pol-components>
] <exc:reduced-char-pol-components>

#exercise[
  Let $L$ be a finite separable extension of $K$ with $(L : K) = n$, and let
  $psi_1, dots, psi_n$ be the distinct embeddings of $L$ into an algebraic
  closure of $K$. Prove that for each $f(X) in L[X]$,
  $
    N_(L slash K) f(X) = product_(i=1)^n psi_i f(X),
  $
  where $psi_i f(X)$ is obtained from $f(X)$ by applying $psi_i$ to each of its
  coefficients.
] <exc:polynomial-norm-embeddings>

#exercise[
  Let $A = M_r (D)$, where $D$ is a skewfield with center $K$. Let $a in A$ be
  given by $a = (alpha_(i j)) in M_r (D)$. Show that
  $
    tr_(A slash K) a = sum_(i=1)^r tr_(D slash K) (alpha_(i i)).
  $
  #hint[@exc:reduced-trace-matrix-ring][Choose $E supset K$ to be a splitting
    field for $D$, and let
    $
      mu : D -> E times.o_K D tilde.equiv M_s (E).
    $
    Then $mu' : A -> E times.o_K A tilde.equiv M_(r s) (E)$ is given by
    $
      mu'(a) = (mu(alpha_(i j)))_(1 <= i, j <= r),
    $
    and
    $
      tr_(A slash K) a & = "trace of" mu'(a)
                         = sum_(i=1)^r "trace of" mu(alpha_(i i)) \
                       & = sum_(i=1)^r tr_(D slash K) (alpha_(i i)).
    $]
  <hint:reduced-trace-matrix-ring>
] <exc:reduced-trace-matrix-ring>
