#import "main-defs.typ": *
#import "statements.typ": *

= Algebraic Preliminaries <ch:algebraic-preliminaries>

#source(10)This chapter reviews some basic algebraic techniques. Proofs are
often omitted, especially when they are readily available in standard
references, or when they are too long or too detailed to warrant their inclusion
in this preliminary chapter. Many readers may wish to glance briefly at the
contents of this chapter, referring back to the relevant sections when they are
needed later. Occasionally, results are stated somewhat more generally than
necessary for later use.

Each ring considered below will be assumed to have a unity element, and each
ring homomorphism preserves unity elements. Every module $M$ over a ring $A$ is
assumed _unital_, that is, the unity element of $A$ acts as identity operator on
$M$. Let $K$ be a commutative ring; a ring $A$ is a _$K$-algebra_ if there is a
ring homomorphism of $K$ into the center of $A$. Such a homomorphism permits us
to view $A$, and all $A$-modules, as $K$-modules. If $A$, $B$ are $K$-algebras,
we call them isomorphic _as $K$-algebras_ if there is a ring isomorphism
$phi: A tilde.equiv B$ such that $phi(alpha x) = alpha phi(x)$, $alpha in K$,
$x in A$. #idx("algebra", "over a commutative ring")#idx("unital")#idx(
  "isomorphism of $K$-algebras",
)#idx("$K$-isomorphism of $K$-algebras")
