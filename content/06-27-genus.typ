#import "main-defs.typ": *
#import "statements.typ": *

== Genus <sec:genus>

Throughout this section let $R$ denote a Dedekind domain with quotient field
$K$. Let $Lambda$ be an $R$-order in a $K$-algebra $A$. Two left
$Lambda$-lattices $M, N$ are in the same _genus_#idx("genus") (notation:
$M samegenus N$) if for each prime ideal $P$ of $R$, there is a
$Lambda_P$-isomorphism $M_P tilde.equiv N_P$.

#theorem[
  Let $M, N$ be left $Lambda$-lattices. Then $M samegenus N$ if and only if for
  each nonzero ideal $I$ of $R$, the condition
  $
    0 -> M -> N -> T -> 0, quad I + ann_R T = R,
  $ <eq:genus-condition>
  holds for some $Lambda$-exact sequence for some $Lambda$-module $T$.
] <th:genus-exact-sequence>

#proof[
  If the condition @eq:genus-condition holds when $I = P$, then
  $P + ann_R T = R$, whence $T_P = 0$ by @th:localization-dedekind. Since
  $
    0 -> M_P -> N_P -> T_P -> 0
  $
  is $Lambda_P$-exact, it follows that $M_P tilde.equiv N_P$. Thus if
  @eq:genus-condition holds when $I$ ranges over the prime ideals of $R$, then
  $M samegenus N$.

  #source(242)Conversely, assume that $M samegenus N$, and let $I$ be a
  preassigned nonzero ideal of $R$. Let $P_1, dots, P_n$ be the distinct prime
  ideals dividing $I$. By the method of proof of
  Exercise~@exc:semilocal-isomorphism, there exists $phi in Hom_Lambda (M, N)$
  such that $phi_(P_i) : M_(P_i) tilde.equiv N_(P_i)$, $1 <= i <= n$. Since
  $
    (ker phi)_(P_i) = ker phi_(P_i) = 0,
  $
  and $ker phi$ is $R$-torsionfree, it follows that $ker phi = 0$. Consider the
  $Lambda$-exact sequence
  $
    0 -> M stretch(->)^phi N -> T -> 0,
  $
  where $T = cok phi$. Then $T_(P_i) = 0$ for $1 <= i <= n$, whence
  $P_i + ann_R T = R$ for each $i$. Therefore $I + ann_R T = R$, as desired.
]

It should be remarked that when $I = R$, the preceding proof is valid if we just
choose $P_1$ to be any prime ideal of $R$.

#corollary[
  Let $L, M, N$ be left $Lambda$-lattices in the same genus. Then there exists a
  left $Lambda$-lattice $L'$ in the genus, such that
  $
    M dotplus N tilde.equiv L dotplus L'.
  $
] <cor:genus-addition>

#proof[
  By @th:genus-exact-sequence, there exist $Lambda$-exact sequences
  $
    0 -> M stretch(->)^phi L -> T -> 0, quad 0 -> N stretch(->)^psi L -> U -> 0,
  $
  such that $T, U$ are $R$-torsion $Lambda$-modules for which
  $
    ann_R T + ann_R U = R.
  $
  Thus for each prime ideal $P$ of $R$, either $T_P = 0$ or $U_P = 0$, that is,
  either $phi_P : M_P tilde.equiv L_P$ or $psi_P : N_P tilde.equiv L_P$. Now
  consider the $Lambda$-exact sequence
  $
    0 -> L' -> M dotplus N limits(-->)^((phi, psi)) L -> 0,
  $
  where $L'$ is defined to be the kernel of the map $(phi, psi)$. The map
  $(phi, psi)$ is epic and split, since for each $P$, the epimorphism
  $(phi, psi)_P : M_P dotplus N_P -> L_P$ is split. Therefore
  $M dotplus N tilde.equiv L dotplus L'$, and it remains for us to prove that
  $L' samegenus L$.

  Let $hat(R)$ be the $P$-adic completion of $R$, where $P$ is a prime ideal of
  $R$, and set $hat(M) = hat(R) times.o_R M$, etc. Then
  $
    hat(M) dotplus hat(N) tilde.equiv hat(L) dotplus hat(L)', quad
    hat(M) tilde.equiv hat(L).
  $
  Since the Krull–Schmidt Theorem holds for finitely generated
  $hat(Lambda)$-modules by Exercise~@exc:krull-schmidt, the above implies (by
  Exercise~@exc:cancellation) that $hat(N) tilde.equiv hat(L)'$. Therefore
  $N_P tilde.equiv L'_P$ by @th:local-completion-comparison, and so
  $L' samegenus N$. This completes the proof.
]

#theorem[
  Let $Lambda$ be a maximal $R$-order in a separable $K$-algebra, and let $M$ be
  any left $Lambda$-ideal in $A$ (always subject to the condition that
  $K M = A$). #source(243)Then $M$ is in the same genus as $Lambda$.
  Furthermore, given any set of left $Lambda$-ideals $M_1, dots, M_r$ in $A$,
  there exists a left ideal $M$ in $Lambda$ such that
  $
    M_1 dotplus dots.c dotplus M_r tilde.equiv Lambda^((r-1)) dotplus M.
  $ <eq:left-ideals-sum>
] <th:left-ideals-genus>

#proof[
  For each $P$, $M_P$ is a principal $Lambda_P$-ideal by
  @th:separable-maximal-principal, and hence $M samegenus Lambda$. By
  @cor:genus-addition, we have $M_1 dotplus M_2 tilde.equiv Lambda dotplus N$
  for some left $Lambda$-lattice $N$ such that $N samegenus Lambda$. But by
  @th:genus-exact-sequence we may embed $N$ in $Lambda$, so replacing $N$ by an
  isomorphic copy, we may assume that $N$ is a left ideal of $Lambda$.
  Continuing in this way, we find after $r - 1$ steps that @eq:left-ideals-sum
  holds for some left ideal $M$ of $Lambda$.
]

#corollary[
  Let $A = M_r (D)$, where $D$ is a skewfield separable over $K$, and let
  $Delta$ be any maximal $R$-order in $D$. For each right ideal $J$ of $Delta$,
  let $Delta' = O_l (J)$, and let
  $
    Lambda = mat(
      delim: "[",
      Delta, dots, Delta, J^(-1);
      , dots, , .;
      Delta, dots, Delta, J^(-1);
      J, dots, J, Delta'
    )
  $
  denote the ring of all $r times r$ matrices $(x_(i j))$, where $x_11$ ranges
  over all elements of $Delta$, $dots, x_(1 r)$ ranges over all elements of
  $J^(-1)$, and so on. Then $Lambda$ is a maximal $R$-order in $A$, and every
  maximal $R$-order is of this form, for some right ideal $J$ of $Delta$.
] <cor:maximal-orders-matrix-form>

#proof[
  By @th:global-maximal-orders-simple, each maximal $R$-order $Lambda$ is of the
  form $Hom_Delta (L, L)$, where $L$ is a right $Delta$-lattice such that
  $K L tilde.equiv D^((r))$. Since $Delta$ is hereditary, $L$ can be written as
  a direct sum of $r$ right ideals of $Delta$. Hence by @th:left-ideals-genus,
  we may take $L = Delta^((r-1)) dotplus J$, where $J$ is a right ideal of
  $Delta$. But we may identify
  $
    Hom_Delta (Delta^((r-1)) dotplus J, quad Delta^((r-1)) dotplus J)
  $
  with the indicated ring of matrices, since there are identifications
  $
    Hom_Delta (Delta, Delta) = Delta, quad Hom_Delta (Delta, J) = J, quad
    Hom_Delta (J, Delta) = J^(-1), quad Hom_Delta (J, J) = Delta'.
  $
  This completes the proof.
]

Let $Lambda$ be a maximal $R$-order in a separable $K$-algebra $A$. We shall say
that the left ideals $M, N$ of $Lambda$ are _relatively prime_ if
$M + N = Lambda$. #idx("relatively prime (ideals)")

#corollary[
  Let $N$ be any left ideal of $Lambda$. Then every class of left
  $Lambda$-ideals in $A$ contains an integral ideal relatively prime to $N$.
] <cor:relatively-prime-representative>

#proof[
  Choose a nonzero $alpha in R inter N$, and let $M$ be any left ideal of
  $Lambda$. Since #source(244)$M samegenus Lambda$, there is an exact sequence
  $
    0 -> M stretch(->)^phi Lambda -> T -> 0
  $
  with
  $
    alpha R + ann_R T = R,
  $
  by @th:genus-exact-sequence. We may write $1 = alpha rho + beta$, with
  $rho in R$, $beta in ann_R T$. Then $beta Lambda subset phi(M)$, and
  $alpha rho in N$, whence $phi(M) + N = Lambda$. But $phi(M) = M x$ for some
  $x in u(A)$, and thus $phi(M)$ lies in the ideal class of $M$. This completes
  the proof.
]

To conclude this section, we prove

#theorem[
  Let $Lambda$ be a maximal $R$-order in a separable $K$-algebra $A$, and let
  $X$ be a left $Lambda$-lattice such that $K X tilde.equiv A^((r))$ for some
  positive integer $r$. Then there exists a left $Lambda$-ideal $M$ in $A$ such
  that
  $
    X tilde.equiv Lambda^((r-1)) dotplus M quad "as" Lambda"-modules."
  $
] <th:lattice-free-plus-ideal>

#proof[
  By hypothesis, there exists an $A$-isomorphism
  $phi : K X tilde.equiv A^((r))$. This isomorphism carries $X$ onto a full
  $R$-lattice $phi(X)$ in $A^((r))$. Since $Lambda^((r))$ is also a full
  $R$-lattice in $A^((r))$, there exists a nonzero $alpha in R$ such that
  $alpha dot phi(X) subset Lambda^((r))$. Replacing $X$ by the isomorphic
  $Lambda$-lattice $alpha dot phi(X)$, we may hereafter assume that
  $
    X subset Lambda^((r)), quad K X = K dot Lambda^((r)) = A^((r)).
  $
  (The above reasoning has also been used in the proof of
  @th:lattice-in-free-module.)

  By @th:global-maximal-hereditary, the maximal order $Lambda$ is hereditary. It
  follows from @th:hereditary-submodules-of-free and @rem:hereditary[(ii)] that
  we may write
  $
    X = M_1 dotplus dots.c dotplus M_r,
  $
  where each $M_i$ is a left ideal of $Lambda$. Since
  $K X = dsum K M_i = A^((r))$, we see that $K M_i = A$ for each $i$, so each
  $M_i$ is a left $Lambda$-ideal in $A$. Hence by @th:left-ideals-genus there
  exists a left $Lambda$-ideal $M$ in $A$ such that
  $
    M_1 dotplus dots.c dotplus M_r tilde.equiv Lambda^((r-1)) dotplus M.
  $
  This completes the proof of the theorem.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

In the following, $Lambda$ denotes an $R$-order in a separable $K$-algebra $A$.
Let ${P_1, dots, P_n}$ be the set of all prime ideals $P$ of $R$ such that
$Lambda_P$ is not a maximal $R_P$-order.

#exercise[
  Let $M, N$ be left $Lambda$-lattices such that $K M tilde.equiv K N$. Prove
  that $M samegenus N$ if and only if
  $
    hat(R)_P times.o_R M tilde.equiv hat(R)_P times.o_R N
  $
  #source(245)for each $P$, where $hat(R)_P$ denotes the $P$-adic completion of
  $R$. \[Remark: If this isomorphism holds for even one $P$, then necessarily
  $K M tilde.equiv K N$. Indeed, the isomorphism implies that
  $
    hat(K)_P times.o_(hat(R)_P) (hat(R)_P times.o_R M) tilde.equiv
    hat(K)_P times.o_(hat(R)_P) (hat(R)_P times.o_R N),
  $
  whence
  $
    hat(K)_P times.o_K K M tilde.equiv hat(K)_P times.o_K K N.
  $
  This implies that $K M tilde.equiv K N$ by the Noether–Deuring Theorem (see
  Curtis–Reiner [@bib:Curtis1962, §~29]).\]
] <exc:genus-completions>

#exercise[
  Let $M, N$ be left $Lambda$-lattices such that $K M tilde.equiv K N$. Prove
  that $M samegenus N$ if and only if
  $
    M_(P_i) tilde.equiv N_(P_i), quad 1 <= i <= n.
  $
] <exc:genus-exceptional-primes>

#exercise[
  Let $0 -> L -> M -> N -> 0$ be an exact sequence of left $Lambda$-lattices.
  Prove that the sequence splits if and only if for $i = 1, dots, n$, the
  sequence
  $
    0 -> L_(P_i) -> M_(P_i) -> N_(P_i) -> 0
  $
  is split.
] <exc:splitting-exceptional-primes>

#exercise[
  Let $M$ be a left ideal of $Lambda$ such that $K M = A$. Show that
  $ord_R Lambda slash M subset M$.
  #hint[@exc:order-ideal-in-ideal][$ord_R Lambda slash M subset
    ann_R Lambda slash M$.] <hint:order-ideal-in-ideal>
] <exc:order-ideal-in-ideal>

#exercise[
  Let $M_1, M_2$ be left ideals of $Lambda$ with $K M_i = A$. Show that if
  $
    ord_R Lambda slash M_1 + ord_R Lambda slash M_2 = R,
  $
  then $M_1 + M_2 = Lambda$. In particular, if $M_1$ and $M_2$ are left ideals
  in a maximal order $Lambda$, then $M_1$ and $M_2$ are "relatively prime"
  whenever their norms are relatively prime. Is the converse true?
] <exc:relatively-prime-norms>

#exercise[
  Let $L, M, N$ be left $Lambda$-lattices such that $L samegenus (M dotplus N)$.
  Show that $L tilde.equiv X dotplus Y$, for some $Lambda$-lattices $X, Y$ such
  that $X samegenus M$, $Y samegenus N$. #hint[@exc:genus-direct-sum][By
    @th:genus-exact-sequence, there exists an $f in Hom_Lambda (L, M dotplus N)$
    such that
    $
      f_P : L_P tilde.equiv M_P dotplus N_P, quad P in {P_1, dots, P_n}.
    $
    Let $pi : M dotplus N -> M$ be the projection map, and set $X = pi f(L)$,
    $Y = ker pi f$. Then
    $
      0 -> Y -> L -> X -> 0
    $
    is an exact sequence of left $Lambda$-lattices. For $P in {P_1, dots, P_n}$,
    the sequence
    $
      0 -> Y_P -> L_P -> X_P -> 0
    $
    is $Lambda_P$-split, since
    $
      L_P tilde.equiv M_P dotplus N_P, quad
      X_P = pi f(L_P) = pi(M_P dotplus N_P) = M_P.
    $
    Therefore, by Exercise~@exc:splitting-exceptional-primes,
    $L tilde.equiv X dotplus Y$, and $X samegenus M$, $Y samegenus N$.]
  <hint:genus-direct-sum>
] <exc:genus-direct-sum>

#exercise[
  Let $L, M$ be left $Lambda$-lattices such that $L samegenus M^((n))$. Then
  there exist $Lambda$-lattices $M_1, dots, M_n samegenus M$ such that
  $
    L tilde.equiv M_1 dotplus dots.c dotplus M_n.
  $
  Further, given any $M_1, dots, M_n samegenus M$, there exists an
  $M' samegenus M$ such that
  $
    M_1 dotplus dots.c dotplus M_n tilde.equiv M^((n-1)) dotplus M'.
  $
  #hint[@exc:genus-multiple-sum][The first assertion follows from
    Exercise~@exc:genus-direct-sum, the second by repeated use of
    @cor:genus-addition.] <hint:genus-multiple-sum>
] <exc:genus-multiple-sum>
