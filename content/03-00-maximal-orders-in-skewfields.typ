#import "main-defs.typ": *
#import "statements.typ": *

= Maximal Orders in Skewfields (Local Case) <ch:maximal-orders-in-skewfields>

#source(144)Throughout this chapter, let $R$ be a _complete discrete valuation
ring_#idx("complete discrete valuation ring")#idx("discrete valuation ring"),
that is, $R$ is a principal ideal domain with a unique maximal ideal
$P = pi R != 0$, and $R$ is complete relative to the $P$-adic valuation. Let $K$
be the quotient field of $R$, and $overline(R) = R slash P$ its residue class
field. We call $K$ a _local_ field#idx("local field"). Let $D$ be a skewfield
whose center contains $K$, such that $(D : K)$ is finite. The aim of this
chapter is to study the structure of maximal $R$-orders in $D$. As we shall see,
the results in this case are surprisingly explicit, and generalize several of
the theorems listed in §~@sec:completions-and-valuations. The presentation below
is based on a beautifully written article by Hasse [@bib:Hasse1931].
