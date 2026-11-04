#import "../main-defs.typ": *

#heading(level: 1, numbering: none)[Permanent notation]

#source(9)
#table(
  columns: (auto, 1fr),
  align: left,
  stroke: none,
  inset: (x: 0pt, y: 0.3em),
  column-gutter: 1.5em,
  [$a | b$], [$a$ divides $b$ (for elements or ideals)],
  [$a divides.not b$], [$a$ does not divide $b$],
  [$card X$], [cardinal number of the set $X$],
  [$A < B$], [$A$ is a proper subset of $B$],
  [$A - J$], [complement of the subset $J$ in the set $A$],
  [$op("char") k$], [characteristic of the field (or ring) $k$],
  [$u(A)$], [group of units of the ring $A$],
  [a.e.], [almost everywhere, that is, except for a finite number of cases],
  [$dsum, dotplus$], [external direct sum],
  [$plus.o$], [internal direct sum],
  [$M | N$], [module $M$ is isomorphic to a direct summand of module $N$],
  [$M^((r))$], [external direct sum of $r$ copies of $M$],
  [$lmodule(A, A)$], [ring $A$ viewed as left $A$-module],
  [$End_A M$], [endomorphism ring of $A$-module $M$],
  [$M_n lr((A))$], [ring of all $n times n$ matrices over a ring $A$],
  [$diag(a_1, dots, a_n)$],
  [diagonal matrix with main diagonal entries $a_1, dots, a_n$],

  [$I, I_n$], [identity matrix (in proper context)],
  [$a_L, a_l thin (a_R, a_r)$],
  [left (right) multiplication by the element $a$],
)

#block(above: 0.6em)[
  #set par(first-line-indent: 0pt, spacing: 0.5em)
  $bold(Z)$ = rational integers, $quad bold(Q)$ = rational field

  $bold(R)$ = real field, $quad bold(C)$ = complex field

  $bold(R)^+ = {alpha in bold(R) : alpha >= 0}$

  $bold(H)$ = quaternion skewfield over $bold(R)$

  $K^* = K - {0}$, where $K$ is a field

  $delta_(i j) = display(cases(1"," & i = j, 0"," & i != j)) quad$ (Kronecker
  delta)
]
