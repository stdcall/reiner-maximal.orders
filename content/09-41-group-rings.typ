#import "main-defs.typ": *
#import "statements.typ": *

== Group rings <sec:group-rings>

We shall collect here some miscellaneous results on integral group rings,
concerned mostly with their relations with maximal orders. Throughout this
section, let $G$ denote a finite group of order $n$, and let $A = K G$ be the
group algebra of $G$ over $K$. We assume once and for all that
$op("char") K divides.not n$, so $A$ is a separable $K$-algebra by
Exercise~@exc:group-algebra-separable. The _integral group ring_ #idx(
  "integral group ring",
)#idx("group ring")$R G$ is the $R$-order in $A$ consisting of all formal sums
$sum_(x in G) alpha_x x$, where the coefficients ${alpha_x}$ lie in $R$. We set
$Lambda = R G$ throughout. Since the study of integral representations of $G$
reduces to the investigation of $Lambda$-modules, it is desirable to know as
much as possible about the $R$-order $Lambda$.

#theorem[
  Let $Gamma$ be any $R$-order in $A$ containing $Lambda$. Then
  $
    Lambda subset Gamma subset n^(-1) Lambda.
  $
  Furthermore,
  $
    Lambda "is maximal" <==> Lambda "is hereditary" <==> n in u(R).
  $
] <th:group-ring-overorders>

#proof[
  Let $T = T_(A slash K)$ be the ordinary trace map. For $x in G$, let
  $x_l: a -> x a$, $a in A$, be left multiplication by $x$. Relative to the
  $K$-basis of $A$ consisting of the elements of $G$, $x_l$ is represented by an
  $n times n$ permutation matrix. If $x != 1$, then all of the main diagonal
  entries of this matrix are 0. This gives
  $
    T_(A slash K) x = cases(n"," & x = 1",", 0"," & x in G"," x != 1".")
  $ <eq:group-algebra-trace>

  #source(389)Now let $gamma = sum_x alpha_x x in Gamma$, where each
  $alpha_x in K$. Since $Gamma$ contains all elements of $G$, we have
  $gamma y^(-1) in Gamma$ for all $y in G$. But $T(gamma y^(-1)) in R$ by
  Exercise~@exc:char-pol-integral, and thus
  $
    T(gamma y^(-1)) = sum_x alpha_x T(x y^(-1)) = n alpha_y in R.
  $
  Therefore $alpha_y in n^(-1) R$ for all $y in G$, whence
  $gamma in n^(-1) dot R G$. This proves that $Gamma subset n^(-1) Lambda$, as
  claimed.

  If $n in u(R)$, the above shows that every order $Gamma$ containing $Lambda$
  must coincide with $Lambda$; thus $Lambda$ is maximal, and also hereditary.
  Conversely, suppose $Lambda$ is hereditary. Then by
  @th:hereditary-center-order, $Lambda$ contains the central idempotent
  $n^(-1) dot sum_(x in G) x$ of $A$. Therefore $n^(-1) in R$, whence
  $n in u(R)$. This completes the proof of the theorem.
]

For the rest of this section, let $Gamma$ denote a maximal order in $A$
containing $Lambda$. We have just shown that $n Gamma subset Lambda$.
Jacobinski's refinement of this result, to be given below, is based on using
reduced traces rather than ordinary traces. Departing slightly from his
terminology, we set #idx("conductor")
$
  (Gamma : Lambda)_l & = {x in A : x Gamma subset Lambda} = "left conductor of"
                       Gamma "into" Lambda, \
  (Gamma : Lambda)_r & = {x in A : Gamma x subset Lambda} = "right conductor of"
                       Gamma "into" Lambda.
$
We shall use the following notation hereafter:
$
  & A = dsum_(i=1)^t A_i quad "(simple components)." \
  & K_i = "center of" A_i, (A_i : K_i) = n_i^2, quad R_i = "integral closure of"
    R "in" K_i. \
  & Gamma = dsum_(i=1)^t Gamma_i, quad Gamma_i = "maximal" R_i"-order in" A_i. \
  & tr_i = tr_(A_i slash K) = "reduced trace from" A_i "to" K. \
  & frak(D)_i = frak(D)(Gamma_i slash R) = "different of" Gamma_i
    "with respect to" R.
$
Let us recall from §~@sec:different-discriminant-global that the inverse
different $frak(D)_i^(-1)$ is the complementary ideal of $Gamma_i$ with respect
to $tr_i$, that is,
$
  frak(D)_i^(-1) = {x in A_i : tr_i (x Gamma_i) subset R}.
$
We note that the right conductor $(Gamma : Lambda)_r$ is a
$(Gamma, Lambda)$-bimodule, and is the largest left $Gamma$-submodule of
$Lambda$.

#theorem(major: true, title: [Jacobinski [@bib:Jacobinski1966]])[
  We have
  $
    (Gamma : Lambda)_l = (Gamma : Lambda)_r = dsum_(i=1)^t (n slash n_i)
    frak(D)_i^(-1).
  $
] <th:group-ring-conductor>

#proof[
  #source(390)Let $tau: A times A -> K$ be the bilinear trace form defined by
  $tau(x, y) = T(x y)$, $x, y in A$, where $T = T_(A slash K)$ as above. Let
  $G = {x_1, dots, x_n}$, $x_1 = 1$, so that ${x_1, dots, x_n}$ is a $K$-basis
  for $A$. From @eq:group-algebra-trace we obtain
  $
    tau(x_i, n^(-1) x_j^(-1)) = delta_(i j) quad "(Kronecker delta)," quad
    1 <= i, j <= n.
  $ <eq:group-algebra-dual-basis>
  Thus ${n^(-1) x_1^(-1), dots, n^(-1) x_n^(-1)}$ is a dual basis to
  ${x_1, dots, x_n}$ relative to $tau$, and so the form $tau$ is nondegenerate.

  Every full $R$-lattice $M$ in $A$ determines a _dual_ lattice #idx(
    "dual of lattice",
  )$tilde(M)$ (see Exercise~@exc:dual-lattice-form), defined by
  $
    tilde(M) = {a in A : tau(a, M) subset R}.
  $
  As shown in Exercise~@exc:dual-lattice-form, the correspondence
  $M -> tilde(M)$ is one-to-one inclusion-reversing, and $tilde(tilde(M)) = M$.
  If $M$ is a _right_ $Gamma$-lattice in $A$, then $tilde(M)$ is a _left_
  $Gamma$-lattice in $A$. If $M$ is $R$-free with basis ${m_i}$, then
  $tilde(M) = dsum R m'_j$, where $tau(m_i, m'_j) = delta_(i j)$,
  $1 <= i, j <= n$. From @eq:group-algebra-dual-basis we conclude at once that
  $
    tilde(Lambda) = dsum_(j=1)^n R n^(-1) x_j^(-1) = n^(-1) Lambda.
  $ <eq:group-ring-dual>

  Now take $M = (Gamma : Lambda)_r$, the largest left $Gamma$-module in
  $Lambda$. Then $tilde(M)$ is the _smallest_ right $Gamma$-module containing
  $tilde(Lambda)$, that is,
  $
    tilde(M) = tilde(Lambda) Gamma = n^(-1) Lambda dot Gamma = n^(-1) Gamma.
  $
  Therefore $M = tilde(tilde(M)) = n tilde(Gamma)$, where
  $
    tilde(Gamma) = {x in A : T(x Gamma) subset R}.
  $

  Each $x in A$ may be written as $x = sum x_i$, $x_i in A_i$. By
  @eq:semisimple-reduced-trace we know that
  $
    T(x) = sum_(i=1)^t n_i tr_i x_i.
  $
  This gives at once
  $
    tilde(Gamma) & = {x in A : n_i tr_i (x_i Gamma_i) subset R quad "for" quad
                     1 <= i <= t} \
                 & = dsum_(i=1)^t n_i^(-1) frak(D)_i^(-1).
  $
  Therefore
  $
    (Gamma : Lambda)_r = n tilde(Gamma) = dsum (n slash n_i) frak(D)_i^(-1),
  $
  as desired. The same argument works equally well for $(Gamma : Lambda)_l$, and
  the theorem is proved.
]

From the preceding we obtain
$
  n Gamma subset n tilde(Gamma) = (Gamma : Lambda)_r subset Lambda,
$
#source(391)so we recover part of @th:group-ring-overorders. From the proof of
@th:group-ring-conductor, we may also show directly that if $Lambda$ is
hereditary, then $Lambda$ is maximal. If $Lambda$ is hereditary, then $Gamma$ is
projective as right $Lambda$-lattice. Hence by @th:derived-context-epic we
obtain
$
  Gamma times.o_Lambda Hom_Lambda (Gamma, Lambda) tilde.equiv End_Lambda Gamma.
$
After making some obvious identifications, we may rewrite this as
$
  Gamma dot (Gamma : Lambda)_l = Gamma.
$
But $(Gamma : Lambda)_l$ is a left $Gamma$-lattice, since it equals
$(Gamma : Lambda)_r$ by @th:group-ring-conductor. Therefore
$(Gamma : Lambda)_l = Gamma$, which implies that $Gamma = Lambda$.

Turning next to questions of ramification, let us first generalize the
definitions given in §§~@sec:dedekind-domains,
@sec:splitting-of-simple-algebras.

#definition[
  Let $B$ be a separable $K$-algebra, and let $P$ be any prime of $K$. We say
  that $B$ is _unramified at $P$_ #idx("unramified")if the $P$-adic completion
  $B_P$ is expressible as
  $
    B_P tilde.equiv dsum M_(n_j) (E_j),
  $
  where for each $j$, $E_j$ is a field which is unramified over the $P$-adic
  field $K_P$. (When $P$ is an infinite prime, this latter condition is taken to
  mean that $E_j = K_P$.)
] <def:unramified-separable-algebra>

#theorem[
  Let $P$ be a maximal ideal of $R$, where $R = algint {K}$ and $K$ is an
  algebraic number field. Then $K G$ is unramified at $P$ whenever
  $P divides.not n R$.
] <th:group-algebra-unramified>

#proof[
  Replacing $R$ by its localization $(R - P)^(-1) R$ and changing notation, we
  may assume that $R$ is the $P$-adic valuation ring in $K$, and that
  $n in u(R)$. Keep the notation introduced before @th:group-ring-conductor. By
  Exercise~@exc:unramified-components, it suffices to show that each $A_i$ is
  unramified at $P$. Keep $i$ fixed; since $n_i | n$ by
  Exercise~@exc:capacity-divides-order, we have $n slash n_i in u(R)$. But
  $n slash n_i in frak(D)_i$ by @th:group-ring-conductor, whence
  $frak(D)_i = Gamma_i$. Therefore
  $
    Gamma_i = frak(D)(Gamma_i slash R_i) dot frak(D)(R_i slash R)
  $
  by Exercise~@exc:different-components, that is,
  $
    frak(D)(Gamma_i slash R_i) = Gamma_i, quad frak(D)(R_i slash R) = R_i.
  $ <eq:group-ring-differents>

  Let $frak(p)$ range over the primes of $R_i$ dividing $P$. By
  @th:different-global-field and the first equality in
  @eq:group-ring-differents, we may conclude that $A_i$ has local index 1 at
  each $frak(p)$. Therefore $A_i$ is unramified at each $frak(p)$. On the other
  hand, from @th:unramified-different and the second equality in
  @eq:group-ring-differents, it follows that each $frak(p)$ is unramified in the
  extension $K_i slash K$. Hence by §~@ss:extensions-of-valuations, each
  $(K_i)_frak(p)$ is unramified over $K_P$. Therefore $A_i$ is unramified at
  $P$, by Exercise~@exc:unramified-over-subfield, and the theorem is
  established.
]

The converse of @th:group-algebra-unramified is false, as we shall see below. It
may well happen that $A$ is unramified at a prime $P$ dividing $n$. We shall
find examples where this occurs by using the next theorem, which is of
importance in its own right.

#theorem(major: true, title: [Schilling])[
  #source(392)#idx("Schilling's Theorem", target: [@th:schilling])Let $G$ be a
  group of order $p^r$, where $p$ is prime, and let $K$ be a field of
  characteristic 0.
  + If $p$ is odd, then each simple component of $K G$ is a full matrix algebra
    over a field.
  + If $p = 2$, then each simple component of $K G$ is of the form $M_k (D)$,
    where $D$ is either a field or a skewfield of index 2.
] <th:schilling>

#proof[
  First let $M_k (D)$ be a simple component of $bold(Q) G$, where $D$ is a
  skewfield with center $L$. Let $omega$ be a primitive $p^r$-th root of 1. By
  Curtis–Reiner [@bib:Curtis1962, (70.8)], $L$ is a subfield of
  $bold(Q)(omega)$. Since $p$ is completely ramified in the extension
  $bold(Q)(omega) slash bold(Q)$, there is a unique prime $P_0$ of $L$ dividing
  $p$ (see references listed in §~@sec:dedekind-domains). Hence by
  @th:group-algebra-unramified, $P_0$ is the only finite prime of $L$ at which
  $M_k (D)$ can possibly ramify. Thus $D$ has local Hasse invariant 0 at every
  finite prime of $L$ except possibly at $P_0$.

  Suppose now that $p$ is odd. Then $D$ has odd index, since this index divides
  $p^r$ by Exercise~@exc:capacity-divides-order. Therefore no infinite prime of
  $L$ ramifies in $D$ by Exercise~@exc:odd-index-unramified-infinite. It follows
  from Exercise~@exc:two-ramified-primes that $D = L$, which proves (i) for the
  case $K = bold(Q)$.

  Now let $p = 2$, and let $D$ have index $m$. Some real primes of $L$ may
  ramify in $D$; at each such prime, the local Hasse invariant of $D$ is
  $1 slash
  2$. But by @eq:sum-of-local-invariants, the sum of _all_ of the local
  invariants of $D$ is 0. This shows that $m = 1$ or 2, and establishes (ii)
  when $K = bold(Q)$.

  Now let $K$ be arbitrary, and let ${B_i}$ range over the simple components of
  $bold(Q) G$. As in the proof of Exercise~@exc:capacity-divides-order, we have
  $
    K G tilde.equiv dsum_(i, j) F_(i j) times.o_(K_i) B_i,
  $
  where $K_i$ is the center of $B_i$. We have just shown that $B_i$ is of the
  form $M_k (D)$, where $D$ is a skewfield of index 1 or 2. Then each
  $F_(i j) times.o_(K_i) B_i$ is also of the form $M_s (D')$, where $D'$ is a
  skewfield of index 1 or 2. This completes the proof.
]

This theorem was rediscovered, with different proofs, by Witt and Roquette; see
also Feit [@bib:Feit1967, (14.5)].

#heading(level: 3, numbering: none, outlined: false)[Exercises]

In Exercises~@exc:capacity-divides-order–@exc:ext-annihilated-by-conductor, we
keep the notation of @th:group-ring-conductor and its proof.

#exercise[
  Show that $n_i | n$ when $op("char") K = 0$.
  #hint[@exc:capacity-divides-order][First take $K = bold(Q)$, $R = bold(Z)$ in
    @th:group-ring-conductor. For each $i$, we have
    $(n slash n_i) frak(D)_i^(-1) subset Gamma_i$, and so
    $n slash n_i in frak(D)_i subset Gamma_i$. Hence $n slash n_i$ is integral
    over $bold(Z)$, whence $n_i | n$. Now let $E$ be any field of
    characteristic~0. Then $E supset bold(Q)$, and
    $
      E G tilde.equiv E times.o_bold(Q) bold(Q) G tilde.equiv dsum_(i=1)^t
      (E times.o_bold(Q) K_i) times.o_(K_i) A_i.
    $
    Fix $i$, and let $E times.o_bold(Q) K_i tilde.equiv dsum F_(i j)$ be a
    direct sum of fields ${F_(i j)}$. Then
    $
      #source(393)\(E times.o_bold(Q) K_i) times.o_(K_i) A_i tilde.equiv
      dsum_j F_(i j) times.o_(K_i) A_i,
    $
    and each summand $F_(i j) times.o A_i$ is a simple algebra of dimension
    $n_i^2$ over its center $F_(i j)$.]
  <hint:capacity-divides-order>
] <exc:capacity-divides-order>

#exercise[
  Let $K$ be an algebraic number field. Prove that for each $i$,
  $
    R_i inter (n slash n_i) frak(D)_i^(-1) = (n slash n_i) frak(D)^(-1)
    (R_i slash R).
  $
  Deduce that
  $
    {x in R : x Gamma subset Lambda} = inter.big_(i=1)^t (n slash n_i)
    (K inter frak(D)^(-1) (R_i slash R)).
  $
  #hint(title: [Jacobinski
    [@bib:Jacobinski1966]])[@exc:conductor-in-ground-ring][By
    Exercise~@exc:different-components, $frak(D)_i = frak(A) frak(B)$ where
    $
      frak(A) = frak(D)(Gamma_i slash R_i), quad
      frak(B) = frak(D)(R_i slash R).
    $
    For $x in R_i$,
    $
      x in (n slash n_i) frak(A)^(-1) frak(B)^(-1) <==>
      x frak(B) subset (n slash n_i) frak(A)^(-1) <==>
      x frak(B) subset (n slash n_i) (K_i inter frak(A)^(-1)).
    $
    Write $K_i inter frak(A)^(-1) = frak(a)^(-1)$, where $frak(a)$ is an ideal
    of $R_i$. If $frak(a) != R_i$, choose a prime ideal $P$ of $R_i$ dividing
    $frak(a)$, and let $frak(P)$ be the prime ideal of $Gamma_i$ corresponding
    to $P$. If $P Gamma_i = frak(P)^e$, then the power of $frak(P)$ in $frak(A)$
    is precisely $frak(P)^(e-1)$. But then
    $
      P supset frak(a) ==> P^(-1) subset frak(a)^(-1) ==>
      P^(-1) subset frak(A)^(-1) ==> P Gamma_i | frak(A),
    $
    a contradiction. Hence $K_i inter frak(A)^(-1) = R_i$, so for $x in R_i$ we
    have
    $
      x in (n slash n_i) frak(D)_i^(-1) <==> x frak(B) subset (n slash n_i) R_i
      <==> x in (n slash n_i) frak(B)^(-1).
    $
    But $(n slash n_i) frak(B)^(-1) subset R_i$, since
    $(n slash n_i) frak(B)^(-1) subset (n slash n_i) frak(D)_i^(-1) subset
    Lambda$, so each element of $(n slash n_i) frak(B)^(-1)$ is integral over
    $R$. This proves the first assertion, and the second is an easy consequence
    of the first.]
  <hint:conductor-in-ground-ring>
] <exc:conductor-in-ground-ring>

#exercise[
  Let $e$ be a central idempotent in $A$, and let $M$ be a left $Lambda$-lattice
  such that $e M = M$. Let
  $
    f_e = inter.big_i (n slash n_i) (K inter frak(D)^(-1) (R_i slash R)),
  $
  where $i$ ranges over all indices such that $e_i$ occurs in $e$. Prove that
  $
    f_e dot Ext_Lambda^1 (M, X) = 0, quad f_e dot Ext_Lambda^1 (X, M) = 0
  $
  for all left $Lambda$-lattices $X$.
  #hint(title: [Jacobinski
    [@bib:Jacobinski1966]])[@exc:ext-annihilated-by-conductor][First reduce the
    problem to the case where $e X = X$. Changing notation, we may then assume
    that $e = 1$. Each $r in f_e$ is an element of $R$ such that
    $r Gamma subset Lambda$. Using the fact that $Gamma$ is hereditary, deduce
    that $r$ annihilates $Ext_Lambda^1 (M, dot)$ and $Ext_Lambda^1 (dot, M)$.]
  <hint:ext-annihilated-by-conductor>
] <exc:ext-annihilated-by-conductor>

(For generalizations of the above, see T. V. Fossum [@bib:Fossum1973b],
Roggenkamp, Huber-Dyson [@bib:Roggenkamp1970b].)

#exercise[
  Let $B = dsum B_i$ (simple components) be a separable $K$-algebra, and let $P$
  be a prime of $K$. Show that $B$ is unramified at $P$ if and only if each
  $B_i$ is unramified at $P$.
] <exc:unramified-components>

#exercise[
  Let $B$ be a central simple $L$-algebra, and let $frak(p)$ be a prime of $L$.
  Show that $B$ is unramified at $frak(p)$ if and only if $B_frak(p)$ is a full
  matrix algebra over $L_frak(p)$, that is, if and only if the local index of
  $B$ at $frak(p)$ equals 1.
] <exc:unramified-local-index>

#exercise[
  #source(394)Let $B$ be a central simple $L$-algebra, and let $K$ be a subfield
  of $L$ such that $(L : K)$ is finite. Let $P$ be a prime of $K$, and let
  $frak(p)$ range over the primes of $L$ dividing $P$. Prove that
  + $B_P tilde.equiv dsum_frak(p) B_frak(p)$, where
    $B_frak(p) = L_frak(p) times.o_L B$ is a central simple $L_frak(p)$-algebra.
  + Let $P$ be a finite prime. Then $B$ is unramified at $P$ if and only if for
    each $frak(p)$, $L_frak(p)$ is unramified over $K_P$ and $B_frak(p)$ is a
    full matrix algebra over $L_frak(p)$.
  + Let $P$ be an infinite prime. Then $B$ is unramified at $P$ if and only if
    for each $frak(p)$, $L_frak(p) = K_P$ and $B_frak(p)$ is a full matrix
    algebra over $L_frak(p)$.

  #hint[@exc:unramified-over-subfield][Write
    $
      B_P tilde.equiv (K_P times.o_K L) times.o_L B, quad
      K_P times.o_K L tilde.equiv dsum_frak(p) L_frak(p),
    $
    where $frak(p)$ ranges over the distinct primes of $L$ dividing $P$.]
  <hint:unramified-over-subfield>
] <exc:unramified-over-subfield>
