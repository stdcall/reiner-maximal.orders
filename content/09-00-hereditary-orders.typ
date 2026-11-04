#import "main-defs.typ": *
#import "statements.typ": *

= Hereditary Orders <ch:hereditary-orders>

#source(360)We shall first present the results of Harada
[@bib:Harada1963a–@bib:Harada1963e]#bib-mentions(
  <bib:Harada1963b>,
  <bib:Harada1963c>,
  <bib:Harada1963d>,
) and Brumer [@bib:Brumer1963] concerning hereditary orders in separable
algebras. The approach used is that of Jacobinski [@bib:Jacobinski1971]. As we
shall see, we can give an explicit description of the structure of hereditary
orders. We can also determine the relationship between a hereditary order and
the maximal orders which contain it. The local theory in
§~@sec:hereditary-orders-local will be applied in
§~@sec:hereditary-orders-global to obtain the global theory of hereditary
orders. In §~@sec:group-rings we consider integral group rings, and prove
several theorems which fit in well with the subject matter of this book.

Throughout this chapter, $R$ denotes a Dedekind domain with quotient field $K$,
and $Lambda$ is an $R$-order in a separable $K$-algebra $A$. Recall that
$Lambda$ is (left) _hereditary_ if every left ideal of $Lambda$ is projective;
by @cor:hereditary-lattices-projective, this occurs if and only if every left
$Lambda$-lattice is projective. Now the ring $Lambda$ is left and right
noetherian, since $Lambda$ is finitely generated as $R$-module. Therefore, as
remarked in @rem:hereditary[(iii)], $Lambda$ is left hereditary if and only if
$Lambda$ is right hereditary. A direct proof of this fact is given in
@th:hereditary-left-right[Theorem] below. Hence in our discussion of hereditary
orders, we may omit the adjectives "left" and "right".
