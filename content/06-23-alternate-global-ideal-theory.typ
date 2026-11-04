#import "main-defs.typ": *
#import "statements.typ": *

== Alternate approach to global ideal theory <sec:alternate-global-ideal-theory>

In §§~@sec:basic-results–@sec:ideal-theory, we derived results on ideals and
orders in the global case by making use of the local theorems from
Chapter~@ch:maximal-orders-over-dvr. In this section we shall give an alternate
approach to some of the global theorems obtained in
§§~@sec:basic-results–@sec:ideal-theory. The direct global approach given below
generalizes some of the standard arguments of algebraic number theory. We shall
not use any of those results from the preceding sections, whose proofs were
based on localization techniques. This section may be skipped if desired without
affecting the continuity of the exposition.

As usual, let $A$ be a separable $K$-algebra, where $K$ is the quotient field of
the Dedekind domain $R$. In §~@sec:ideal-theory, we defined prime ideals of an
$R$-order $Lambda$ in $A$, and showed that these coincide with the maximal
two-sided ideals of $Lambda$. We now recall some other definitions from
§~@sec:ideal-theory. All ideals $M$ considered below are assumed to be full
$R$-lattices in $A$. Call $M$ a _normal ideal_ if $O_l (M)$ is a maximal
$R$-order. An _integral ideal_ is a normal ideal $M$ such that
$M subset O_l (M)$. A _maximal integral ideal_ is an integral ideal $M$ which is
a maximal left ideal in $O_l (M)$. (We shall eventually remedy this asymmetry in
the definitions (see @lem:ideal-in-left-iff-right-order,
@th:left-right-orders-maximal-direct, and @th:maximal-left-right-ideal-direct).)
Let us write $M = M_(i j)$ to indicate that $M$ is an ideal with
$
  O_l (M_(i j)) = Lambda_i, quad O_r (M_(i j)) = Lambda_j.
$
Our aim is to derive the factorization properties of one-sided and two-sided
ideals. We begin with

#lemma[
  Let $Lambda$ be any $R$-order in $A$. Then every two-sided ideal in $Lambda$
  contains a product of prime ideals.
] <lem:ideal-contains-prime-product>

#proof[
  If not, then the set of two-sided ideals which do not contain such products is
  non-empty, hence has a maximal element $J$ since $Lambda$ is noetherian.
  Clearly $J$ is not a prime ideal, so by @eq:prime-ideal-quotient-condition
  there exist two-sided ideals $B$, $C$ of $Lambda$, properly containing $J$,
  such that $J supset B C$. But both $B$ and $C$ contain products of prime
  ideals, whence so does $J$. This yields a contradiction, and proves the lemma.
]

#lemma[
  Let $M_(i j)$ be a full $R$-lattice in $A$. Then $M_(i j) subset Lambda_i$ if
  and only if $M_(i j) subset Lambda_j$.
] <lem:ideal-in-left-iff-right-order>

#proof[
  #source(214)Let $M_(i j) subset Lambda_i$; then
  $
    M_(i j) dot M_(i j) subset Lambda_i dot M_(i j) = M_(i j)
    ==> M_(i j) subset O_r (M_(i j)) = Lambda_j.
  $
  This completes the proof.
]

For any full $R$-lattice $L = L_(i j)$ in $A$, define $L^(-1)$ as in
@eq:inverse-lattice. Then for $x in L^(-1)$,
$
  L x subset Lambda_i ==> L dot x Lambda_i subset Lambda_i
  ==> x Lambda_i subset L^(-1),
$
whence $L^(-1)$ is a right $Lambda_i$-module. Thus we obtain
$
  O_r (L_(i j)^(-1)) supset Lambda_i, quad O_l (L_(i j)^(-1)) supset Lambda_j.
$ <eq:inverse-lattice-orders>

Our next step is to develop the theory of two-sided ideals, and we now prove

#lemma[
  Let $M$ be a two-sided ideal in the maximal order $Lambda$. If $M < Lambda$,
  then $M^(-1) > Lambda$.
] <lem:two-sided-ideal-inverse-larger>

#proof[
  It is clear from @eq:inverse-lattice-orders that $M^(-1)$ is a two-sided
  $Lambda$-ideal in $A$, and obviously $M^(-1) supset Lambda$. Let us assume
  that $M^(-1) = Lambda$, and obtain a contradiction. Since $M < Lambda$, we can
  choose a prime ideal $frak(P)$ of $Lambda$ with
  $M subset frak(P) subset Lambda$. Let $alpha$ be a nonzero element of
  $R inter frak(P)$ (such exist, since $frak(P)$ is a full $R$-lattice in $A$).
  Then by @lem:ideal-contains-prime-product $alpha Lambda$ contains a product of
  prime ideals, and so we may write
  $
    frak(P) supset alpha Lambda supset frak(P)_1 frak(P)_2 dots.c frak(P)_r,
  $
  where the $frak(P)_i$ are prime ideals, and where $r$ is minimal. Since
  $frak(P) supset frak(P)_1 dots.c frak(P)_r$ and $frak(P)$ is a prime ideal, it
  follows that $frak(P)$ contains some factor $frak(P)_j$, and then of course
  $frak(P) = frak(P)_j$. Thus we may write
  $
    frak(P) supset alpha Lambda supset B frak(P) C,
  $
  where $B, C$ are two-sided ideals of $Lambda$. We then obtain
  $
    alpha^(-1) B frak(P) C subset Lambda
    & ==> B dot alpha^(-1) frak(P) C dot B subset B
    ==> alpha^(-1) frak(P) C B subset O_r (B) \
    & ==> alpha^(-1) C B subset frak(P)^(-1) subset M^(-1) = Lambda
    ==> C B subset alpha Lambda.
  $
  This shows that $alpha Lambda$ contains a product $C B$ of $r - 1$ prime
  ideals, which contradicts the minimality of $r$, and completes the rather
  mystifying proof.
]

#theorem[
  Let $M$ be a full $R$-lattice in $A$ such that $O_l (M)$ is a maximal order.
  Then
  $
    M dot M^(-1) = O_l (M).
  $
] <th:lattice-times-inverse>

#proof[
  Let $Lambda = O_l (M)$ be maximal, and set $B = M dot M^(-1)$, a two-sided
  ideal in $Lambda$. Then
  #source(215)
  $
    B B^(-1) subset Lambda ==> M dot M^(-1) B^(-1) subset Lambda
    ==> M^(-1) B^(-1) & subset M^(-1) \
                      & ==> B^(-1) subset O_r (M^(-1)).
  $
  But $O_r (M^(-1)) supset O_l (M) = Lambda$ by @eq:inverse-lattice-orders,
  whence $O_r (M^(-1)) = Lambda$. Therefore $B^(-1) subset Lambda$, so
  $B = Lambda$ by @lem:two-sided-ideal-inverse-larger. This completes the proof.
]

The preceding result is the key step in this chain of arguments. Using it, we
prove

#theorem[
  Let $Lambda$ be a maximal order. For each two-sided ideal $M$ in $Lambda$, we
  have
  $
    M dot M^(-1) = M^(-1) dot M = Lambda, quad (M^(-1))^(-1) = M.
  $ <eq:two-sided-ideal-inverse>
  Furthermore, every two-sided ideal in $Lambda$ is uniquely expressible as a
  product of prime ideals of $Lambda$, and multiplication of prime ideals is
  commutative.
] <th:two-sided-ideals-factorization>

#proof[
  The first two equalities in @eq:two-sided-ideal-inverse are immediate
  consequences of @th:lattice-times-inverse. To establish the last formula,
  choose a nonzero $alpha in R$ such that $alpha M^(-1) subset Lambda$. Then
  $alpha M^(-1)$ is a two-sided ideal of $Lambda$, whence
  $
    (alpha M^(-1)) (alpha M^(-1))^(-1) = Lambda.
  $
  But
  $
    (alpha M^(-1))^(-1) = alpha^(-1) L, quad "where" quad L = (M^(-1))^(-1).
  $
  Therefore $M^(-1) dot L = Lambda$, whence
  $
    L = Lambda L = M M^(-1) dot L = M Lambda = M.
  $

  We shall now show that every two-sided ideal $N$ of $Lambda$ is a product of
  prime ideals (an "empty" product, if $N = Lambda$.) If the result is false,
  let $N$ be a largest counterexample. Surely $N$ is not prime, and so there
  exists a prime ideal $frak(P)$ with $N < frak(P) < Lambda$, and hence
  $
    N subset N frak(P)^(-1) subset Lambda.
  $
  If $N = N frak(P)^(-1)$, then $frak(P)^(-1) subset O_r (N) = Lambda$, which is
  impossible by @lem:two-sided-ideal-inverse-larger. Thus $N < N frak(P)^(-1)$,
  whence $N frak(P)^(-1)$ is a product of prime ideals
  $frak(P)_1 dots.c frak(P)_r$. This gives
  $N = frak(P)_1 dots.c frak(P)_r frak(P)$, a contradiction. We have thus
  established that every two-sided ideal of $Lambda$ is a product of prime
  ideals.

  Now let $frak(P)$, $frak(P)'$ be distinct prime ideals of $Lambda$. Then
  $
    frak(P)^(-1) frak(P)' frak(P) subset frak(P)^(-1) Lambda frak(P) = Lambda,
  $
  and
  $
    frak(P) (frak(P)^(-1) frak(P)' frak(P)) = frak(P)' frak(P) subset frak(P)'.
  $
  Thus $frak(P)'$ contains the product $frak(P) (frak(P)^(-1) frak(P)' frak(P))$
  of a pair of two-sided ideals of $Lambda$, and consequently
  $frak(P)' supset frak(P)^(-1) frak(P)' frak(P)$. Therefore
  $frak(P) frak(P)' supset frak(P)' frak(P)$. Since the reverse #source(
    216,
  )inclusion follows by symmetry, we obtain
  $frak(P) frak(P)' = frak(P)' frak(P)$, as desired. It remains to prove
  uniqueness (up to order of occurrence of the factors), so let
  $
    frak(P)_1 dots.c frak(P)_r = frak(Q)_1 dots.c frak(Q)_s,
  $ <eq:two-prime-factorizations>
  where the $frak(P)$'s and $frak(Q)$'s are prime ideals. Then
  $frak(P)_1 supset product frak(Q)_i$ implies that $frak(P)_1 = frak(Q)_k$ for
  some $k$. Multiplying @eq:two-prime-factorizations by $frak(P)_1^(-1)$ and
  repeating the argument, we see that the ${frak(P)_i}$ coincide with the
  ${frak(Q)_j}$, apart from order of occurrence. This establishes the theorem.
]

It is easily deduced from the above that the set of two-sided $Lambda$-ideals in
$A$ is the free abelian group generated by the prime ideals of $Lambda$. We
leave the obvious proofs to the reader.

#remark(numbered: false)[
  The method of proof of @th:lattice-times-inverse can be applied to more
  general situations, and leads to the theory of Asano orders in arbitrary
  rings. As in Jacobson [@bib:Jacobson1943, Ch.~6], one first generalizes the
  concepts of orders and fractional ideals. Then one defines an _Asano
  order_#idx("Asano order") to be an order whose fractional two-sided ideals
  form a multiplicative group. For the theory of Asano orders, the reader may
  consult Jacobson [@bib:Jacobson1943] as basic reference. Further developments
  are given in Asano [@bib:Asano1939, @bib:Asano1949], Harada
  [@bib:Harada1964a], Michler [@bib:Michler1969], and Robson [@bib:Robson1968,
  @bib:Robson1972].
]

#corollary[
  If $M$ is a proper left ideal of the maximal order $Lambda$, then
  $M^(-1) > Lambda$.
] <cor:left-ideal-inverse-larger>

#proof[
  Let $M subset N subset Lambda$, where $N$ is a maximal left ideal of $Lambda$.
  Then $M^(-1) supset N^(-1) supset Lambda$, and so it suffices to prove that
  $N^(-1) > Lambda$. Let us set
  $
    frak(P) = ann_Lambda Lambda slash N.
  $
  As in the proof of @th:maximal-left-ideal-prime, we find that $frak(P)$ is a
  prime ideal of $Lambda$, and $Lambda slash N$ is a simple left module over the
  simple ring $overline(Lambda) = Lambda slash frak(P)$. Hence $N$ is the
  inverse image, under the map $Lambda -> overline(Lambda)$, of some maximal
  left ideal of $overline(Lambda)$. Therefore (see
  Exercise~@exc:maximal-ideals-conjugate) we may write
  $
    N = Lambda (1 - e) + frak(P),
  $
  where $e in Lambda$ is such that its image $overline(e)$ is a primitive
  idempotent in $overline(Lambda)$. Set $L = e Lambda + frak(P)$, a right ideal
  in $Lambda$. Since $(1 - e) e in frak(P)$, it follows that
  $N dot L subset frak(P)$. On the other hand, $N dot L$ is a two-sided ideal of
  $Lambda$ containing $frak(P)^2$. It follows from
  @th:two-sided-ideals-factorization that $N L$ is either $frak(P)$ or
  $frak(P)^2$. If $N L = frak(P)^2$, then $frak(P) e subset frak(P)^2$;
  multiplying by $frak(P)^(-1)$, we deduce that $e in frak(P)$, which is
  impossible. This shows that $N L = frak(P)$.

  Now choose a nonzero $alpha in R inter frak(P)$, and write $alpha Lambda$ as a
  product of prime ideals of $Lambda$. Since $alpha Lambda subset frak(P)$, one
  of the factors must equal $frak(P)$, and so we may write
  $
    alpha Lambda = frak(P) frak(Q) = N L frak(Q),
  $
  #source(217)where $frak(Q)$ is some two-sided ideal of $Lambda$. If
  $N^(-1) = Lambda$, then
  $
    alpha^(-1) L frak(Q) subset N^(-1) = Lambda
    & ==> L frak(Q) subset alpha Lambda
    ==> L Lambda subset alpha Lambda dot frak(Q)^(-1) = frak(P) \
    & ==> L subset frak(P).
  $
  But $L = e Lambda + frak(P)$, so the last inclusion is impossible. This shows
  that $N^(-1) > Lambda$, and completes the proof of the corollary.
]

We are finally ready to prove

#theorem[
  Let $M$ be a full $R$-lattice in $A$. Then $O_l (M)$ is a maximal order if and
  only if $O_r (M)$ is a maximal order.
] <th:left-right-orders-maximal-direct>

#proof[
  Let $Lambda = O_l (M)$ be maximal. Replacing $M$ by $alpha M$ if need be,
  where $alpha in R$, $alpha != 0$, we may hereafter assume that
  $M subset Lambda$. When $M = Lambda$, then $O_r (M) = Lambda$, so we may
  restrict ourselves to the case where $M < Lambda$. If the theorem is false,
  let $M$ be a maximal counterexample, and choose a left ideal $L$ of $Lambda$
  such that
  $
    M < L subset Lambda, quad L slash M = "simple left" Lambda"-module".
  $
  (Possibly $L = Lambda$.) Then $O_l (L) = Lambda$, and since $M$ is assumed to
  be a maximal counterexample, it follows that $O_r (L) = Lambda'$ is a maximal
  order. Then $L dot L^(-1) = Lambda$ by @th:lattice-times-inverse. But the
  analogue of @th:lattice-times-inverse, obtained by reversing "left" and
  "right", is also true. This analogue yields the equality
  $L^(-1) dot L = Lambda'$, since $O_r (L)$ is a maximal order.

  Each left ideal $X$ of $Lambda'$ maps onto a $Lambda$-submodule $L X$ of $L$,
  and the correspondence $X <-> L X$ is one-to-one, since $X = L^(-1) dot L X$.
  Set $N = L^(-1) M$; then
  $
    N = L^(-1) M subset L^(-1) L = Lambda'.
  $
  It follows that $N$ is a maximal left ideal of $Lambda'$, since $M$ is a
  maximal $Lambda$-submodule of $L$. Consequently we obtain
  $
    N^(-1) > Lambda', quad N dot N^(-1) = Lambda', quad
    N^(-1) dot N subset O_r (N),
  $
  by @cor:left-ideal-inverse-larger and @th:lattice-times-inverse.

  Next, for $x in A$ we have
  $
    N x subset N ==> L N x subset L N ==> x in O_r (M), \
    M x subset M ==> L^(-1) M x subset L^(-1) M ==> x in O_r (N).
  $
  Therefore $O_r (N) = O_r (M)$. Since $M$ is assumed to be a counterexample to
  the theorem, it follows that $O_r (N)$ is not a maximal order. Thus
  $O_r (N) < Lambda''$ for some maximal order $Lambda''$. We observe next that
  $N Lambda'' N^(-1)$ is an order, since
  #source(218)
  $
    N Lambda'' N^(-1) dot N Lambda'' N^(-1)
    subset N Lambda'' dot O_r (N) dot Lambda'' N^(-1)
    subset N Lambda'' N^(-1).
  $
  But also
  $
    N Lambda'' N^(-1) supset N dot N^(-1) = Lambda',
  $
  and hence $N Lambda'' N^(-1) = Lambda'$, since $Lambda'$ is a maximal order.
  Consequently there is a chain of left $Lambda'$-ideals
  $
    N subset N Lambda'' subset N Lambda'' N^(-1) = Lambda'.
  $
  Since $N$ is a maximal left ideal in $Lambda'$, it follows that $N Lambda''$
  is either $N$ or $Lambda'$. If $N Lambda'' = N$, then
  $Lambda'' subset O_r (N)$, which is impossible. Hence $N Lambda'' = Lambda'$,
  and thus
  $
    Lambda' = N Lambda'' dot N^(-1) = Lambda' N^(-1).
  $
  Therefore $N^(-1) = Lambda'$, which is also impossible. This proves that there
  can be no counterexample to the theorem, and so the result is established.
]

We have now shown, without the use of local results, that for a normal ideal
$M$, both $O_l (M)$ and $O_r (M)$ are maximal orders. We have also shown that
$
  M dot M^(-1) = O_l (M), quad M^(-1) dot M = O_r (M)
$
for any normal ideal $M$, and furthermore, $M subset O_l (M)$ if and only if
$M subset O_r (M)$. The proofs of
@th:global-proper-product-factorization[Theorem] and
@th:to-contain-is-to-divide[Theorem] carry over unchanged, since they depend
only upon the above-stated results, rather than any localization arguments. We
are left with the task of proving @th:global-maximal-integral-both-sides without
using results from Chapter~@ch:maximal-orders-over-dvr.

#theorem[
  Let $M = M_12$ be a normal ideal. Then $M$ is a maximal left ideal in
  $Lambda_1$ if and only if $M$ is a maximal right ideal in $Lambda_2$.
] <th:maximal-left-right-ideal-direct>

#proof[
  Let $M$ be a maximal left ideal in $Lambda_1$. Then $M subset Lambda_2$, by
  @lem:ideal-in-left-iff-right-order. If $M = Lambda_2$, then
  $Lambda_1 = O_l (M) = Lambda_2 = M$, which is impossible. Suppose that $M$ is
  not a maximal right ideal of $Lambda_2$. Then there exists a normal ideal
  $N = N_32$ such that
  $
    M_12 < N_32 < Lambda_2.
  $
  Surely $N_32 < Lambda_3$, since otherwise $Lambda_2 = Lambda_3 = N$. It
  follows from @th:to-contain-is-to-divide that we may write
  $M_12 = B_13 dot N_32$ for some integral ideal $B_13$. The product $B dot N$
  is a proper product, whence by Exercise~@exc:proper-product-criterion we
  obtain
  $
    M = B dot N < B dot Lambda_3 = B subset Lambda_1.
  $
  Therefore $B = Lambda_1$, and so $Lambda_3 = O_r (B) = Lambda_1$, which
  implies that $M = B dot N = Lambda_3 dot N_32 = N$. This is a contradiction
  and the theorem is proved.
]

At this point we have established all of the major results of
§~@sec:ideal-theory without the use of localization arguments. We shall not
proceed further with the program #source(219)of obtaining global results
directly however, and merely observe that the remaining theorems in
§~@sec:ideal-theory can be derived readily from the results so far established
in this section.
