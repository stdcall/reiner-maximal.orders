#import "main-defs.typ": *
#import "statements.typ": *

== Different, discriminant <sec:different-discriminant-local>

Throughout this section, $R$ denotes a discrete valuation ring, not necessarily
complete, and $Lambda$ a maximal $R$-order in a central simple $K$-algebra $A$.
Let $tr_(A slash K)$ denote the reduced trace map, and
$tau_(A slash K) : A times A -> K$ the bilinear reduced trace form defined by
$tau(a, b) = tr(a b)$. We shall drop the subscript $A slash K$ when there is no
danger of confusion.

We define
$
  tilde(Lambda) = {x in A : tau(x, Lambda) subset R}
  = {x in A : tr(x Lambda) subset R}.
$
By Exercise~@exc:dual-lattice-form, $tilde(Lambda)$ is a full $R$-lattice in
$A$, and is clearly a two-sided $Lambda$-module containing $Lambda$ (by
@th:reduced-integral). Let $frak(P) = rad Lambda$; then by
@th:two-sided-ideals-cyclic we have $tilde(Lambda) = frak(P)^(-m)$ for some
$m >= 0$. Call $tilde(Lambda)$ the _inverse different_#idx("inverse different"),
and define the _different_#idx("different")
$
  frak(D) = frak(D)(Lambda slash R) = frak(P)^m.
$

#theorem[
  If $hat(R)$ is the $P$-adic completion of $R$, then
  $
    frak(D)(hat(Lambda) slash hat(R))
    = hat(R) times.o_R frak(D)(Lambda slash R).
  $
] <th:different-completion>

#proof[
  By @eq:reduced-trace-norm-ground-field, $tr_(hat(A) slash hat(K))$ extends the
  map $tr_(A slash K)$. Hence for each $x in A$ we have
  #source(194)
  $
    tr_(A slash K) (x Lambda) subset R <==>
    tr_(hat(A) slash hat(K)) (x Lambda) subset hat(R) <==>
    x in tilde(hat(Lambda)).
  $
  This proves that $tilde(Lambda) = A inter tilde(hat(Lambda))$. If
  $frak(P) = rad Lambda$, then $frak(P) = A inter hat(frak(P))$, where
  $hat(frak(P)) = rad hat(Lambda)$. Thus if
  $tilde(hat(Lambda)) = hat(frak(P))^(-k)$, then $tilde(Lambda) = frak(P)^(-k)$.
  This gives the desired result. For later use, we remark that the proof is
  equally valid for the more general case where $A$ is a separable $K$-algebra.
]

#theorem[
  Let $A = M_r (D)$, where $D$ is a skewfield with center $K$, and let
  $Lambda = M_r (Delta)$, where $Delta$ is a maximal $R$-order in $D$. Then
  $
    frak(D)(Lambda slash R) = frak(D)(Delta slash R) dot Lambda.
  $
] <th:different-matrix-order>

#proof[
  Let $x = (d_(i j)) in M_r (D)$, and let
  $lambda = (beta_(i j)) in M_r (Delta)$. Then by
  Exercise~@exc:reduced-trace-matrix-ring,
  $
    tr_(A slash K) (x lambda) = sum_(i, j) tr_(D slash K) (d_(i j) beta_(j i)).
  $
  Hence if each $d_(i j) in tilde(Delta)$, then $x in tilde(Lambda)$. On the
  other hand, let $lambda$ have entry $beta$ at position $(k, l)$, and zeros
  elsewhere, with $beta$ variable in $Delta$. Then
  $tr_(A slash K) (x lambda) = tr_(D slash K) (d_(l k) beta)$, so if
  $x in tilde(Lambda)$ then $d_(l k) in tilde(Delta)$. This proves that
  $tilde(Lambda) = M_r (tilde(Delta))$. If $tilde(Delta) = (rad Delta)^(-m)$,
  then
  $
    tilde(Lambda) = M_r ((rad Delta)^(-m)) = {M_r (rad Delta)}^(-m)
    = {rad Lambda}^(-m),
  $
  which proves the theorem.
]

Together, these results yield

#theorem[
  Let $hat(K) times.o_K A tilde.equiv M_t (E)$, where $E$ is a skewfield with
  center $hat(K)$ and index $m$, that is, $m^2 = (E : hat(K))$. Suppose that the
  residue class field $overline(R)$ is finite. Then
  $
    frak(D)(Lambda slash R) = frak(P)^(m-1).
  $
] <th:local-different>

#proof[
  By @th:different-completion it suffices to prove that
  $frak(D)(hat(Lambda) slash hat(R)) = hat(frak(P))^(m-1)$. Now $hat(Lambda)$ is
  a maximal $hat(R)$-order in $M_t (E)$, so by
  @cor:complete-local-maximal-endomorphisms we may write
  $hat(Lambda) = M_t (Omega)$ for some maximal $hat(R)$-order $Omega$ in $E$. By
  @th:different-matrix-order we obtain
  $
    frak(D)(hat(Lambda) slash hat(R)) = frak(D)(Omega slash hat(R)) dot
    hat(Lambda).
  $
  But $frak(D)(Omega slash hat(R)) = (rad Omega)^(m-1)$ by
  @th:local-skewfield-different, which completes the proof.
]

For any left ideal $L$ of $Lambda$, define its _norm_#idx("norm (of ideal)") as
$
  N_(A slash K) (L) = ord_R Lambda slash L.
$

#theorem[
  The discriminant $d(Lambda slash R)$ is given by
  $
    d(Lambda slash R) = N_(A slash K) (frak(D)(Lambda slash R)).
  $
] <th:local-discriminant-norm-different>

#proof[
  #source(195)Both the discriminant and the different behave properly under the
  passage from $R$ to $hat(R)$, by @th:different-completion and
  Exercise~@exc:discriminant-base-change. So likewise does the norm, and thus it
  suffices to prove the result for the case where $R$ is complete. But then
  $Lambda tilde.equiv M_t (Omega)$ as in the proof of @th:local-different, and
  $frak(D)(Lambda slash R) = pi_Omega^k dot Lambda$ for some $k$. Therefore
  $
    N(frak(D)(Lambda slash R)) = ord_R Lambda slash pi_Omega^k Lambda
    = ord_R pi_Omega^(-k) Lambda slash Lambda
    = ord_R tilde(Lambda) slash Lambda.
  $
  The rest of the proof is exactly like that of
  @lem:skewfield-discriminant-norm-different.
]
