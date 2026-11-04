#import "main-defs.typ": *
#import "statements.typ": *

= Maximal Orders over Discrete Valuation Rings <ch:maximal-orders-over-dvr>

#open-section()
#source(179)Throughout this chapter, $R$ denotes a discrete valuation ring with
quotient field $K$, maximal ideal $P = pi R != 0$, and residue class field
$overline(R) = R slash P$. We have already seen in @th:maximal-orders-components
that the study of maximal $R$-orders in separable $K$-algebras can be reduced to
the case of central simple algebras. We shall investigate this case in detail
here, by using the results from Chapter~@ch:maximal-orders-in-skewfields on
maximal orders in skewfields, and then applying the Morita equivalence between
skewfields and full matrix algebras over skewfields.

We assume throughout that $A$ is a central simple $K$-algebra, and that $V$ is a
minimal left ideal of $A$. Set $D = Hom_A (V, V)$, and view $lmodule(A, V)_D$ as
a bimodule. If ${v_1, dots, v_r}$ is any right $D$-basis for $V$, then for each
$a in A$ we may write
$
  a(v_1, dots, v_r) = (v_1, dots, v_r)(alpha_(i j)), quad
  (alpha_(i j)) in M_r (D),
$ <eq:central-simple-matrix-form>
and the map defined by $a -> (alpha_(i j))$ permits us to identify $A$ with
$M_r (D)$.

Likewise, if $Delta$ is an $R$-order in $D$, we may choose a free
$Delta$-lattice in $V$, say $M = dsum_(i=1)^r m_i Delta$. For each
$a in Hom_Delta (M, M)$ we may write
$
  a(m_1, dots, m_r) = (m_1, dots, m_r)(alpha_(i j)), quad
  (alpha_(i j)) in M_r (Delta).
$ <eq:order-matrix-form>
The map defined by $a -> (alpha_(i j))$ then gives an identification of
$Hom_Delta (M, M)$ with $M_r (Delta)$, and this identification is consistent
with that obtained from @eq:central-simple-matrix-form. Finally, we set
$
  (D : K) = n^2, quad (A : K) = n^2 r^2.
$
