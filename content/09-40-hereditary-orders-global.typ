#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/09-40-hereditary-orders-global.typ": evaluation-square

== Global theory of hereditary orders <sec:hereditary-orders-global>

#source(376)Keeping the notation introduced at the start of this chapter, we
assume now that $R$ is any Dedekind domain. Here we shall develop the theory of
hereditary $R$-orders, by using the local results obtained in
§~@sec:hereditary-orders-local. We prove first

#theorem[
  $Lambda$ is left hereditary if and only if $Lambda$ is right hereditary.
] <th:hereditary-left-right>

#proof[
  Since $Lambda$ is both left and right noetherian, the result is a special case
  of @rem:hereditary[(iii)]. We give an independent proof here. Each left
  $Lambda$-lattice $M$ determines a _dual_ #idx("dual of lattice")$M^* =
  Hom_R (M, R)$, which is a right $Lambda$-lattice, and there is a natural
  isomorphism $M tilde.equiv M^(**)$ (see Exercise~@exc:lattice-duality).
  Furthermore, any exact sequence of left $Lambda$-lattices
  $
    0 -> L -> M -> N -> 0
  $ <eq:lattice-sequence>
  must be $R$-split, since $N$ is $R$-projective by @th:steinitz. Hence when we
  apply $Hom_R (dot, R)$ to @eq:lattice-sequence, the resulting sequence
  $
    0 -> N^* -> M^* -> L^* -> 0
  $ <eq:dual-lattice-sequence>
  is also $R$-split, and hence exact. The maps in @eq:dual-lattice-sequence are
  right $Lambda$-homomorphisms. Conversely, taking duals in
  @eq:dual-lattice-sequence gives @eq:lattice-sequence again. Hence the sequence
  @eq:lattice-sequence is $Lambda$-split if and only if
  @eq:dual-lattice-sequence is $Lambda$-split.

  Suppose now that $Lambda$ is right hereditary, and let $N$ be any left ideal
  of $Lambda$. Then we can find a $Lambda$-exact sequence @eq:lattice-sequence
  in which $M$ is a free left $Lambda$-lattice. Now $L^*$ is a right
  $Lambda$-lattice, hence is $Lambda$-projective by
  @cor:hereditary-lattices-projective. Therefore the sequence
  @eq:dual-lattice-sequence is $Lambda$-split, whence so is
  @eq:lattice-sequence. This proves that every left ideal of $Lambda$ is
  projective, so $Lambda$ is left hereditary. The theorem now follows by an
  obvious symmetry argument.
]

#theorem[
  Let $Lambda subset Lambda'$ be $R$-orders in $A$. If $Lambda$ is hereditary,
  then so is $Lambda'$.
] <th:hereditary-overorder>

#proof[
  Given any left $Lambda'$-lattice $L$, there is an exact sequence of left
  $Lambda'$-lattices
  $
    0 -> M -> F stretch(->)^phi L -> 0
  $
  with $F$ $Lambda'$-free. Since $L$ is also a left $Lambda$-lattice, hence
  $Lambda$-projective, the sequence is $Lambda$-split. Therefore there exists a
  map $psi in Hom_Lambda (L, F)$ such that $phi psi = 1$ on $L$. But
  Exercise~@exc:overorder-homomorphisms shows that $psi$ is a
  $Lambda'$-homomorphism, whence the above sequence is $Lambda'$-split.
  Therefore $L$ is $Lambda'$-projective, which completes the proof that
  $Lambda'$ is hereditary.
]

It should be pointed out that the preceding theorems and their proofs are valid
without the hypothesis that $A$ be a separable $K$-algebra. For the #source(
  377,
)remainder of this section, however, we shall keep our hypothesis that $A$ is
separable. We intend to investigate $R$-orders $Lambda$ by considering their
$P$-adic completions $Lambda_P$, where $P$ ranges over all maximal ideals of
$R$. As a first step in this direction, we show

#theorem[
  $Lambda$ is hereditary if and only if $Lambda_P$ is hereditary for all $P$, or
  equivalently, if and only if $Lambda_P$ is an extremal $R_P$-order in $A_P$
  for all $P$.
] <th:hereditary-iff-completions-extremal>

#proof[
  Note first that since $A$ is $K$-separable, $A_P$ is $K_P$-separable for each
  $P$, by Exercise~@exc:separable-base-change. We showed in
  @cor:hereditary-local that $Lambda$ is hereditary if and only if each
  localization $(R - P)^(-1) Lambda$ is hereditary. The same argument works if
  we use completions rather than localizations. Alternatively, we saw in
  §~@sec:localization that $Lambda$ is hereditary if and only if
  $dim Lambda <= 1$, where "dim" means "left global dimension". By
  @th:global-dimension-local and @th:dimension-completion,
  $
    dim Lambda = sup_P {dim Lambda_P}.
  $
  This again shows that $Lambda$ is hereditary if and only if each $Lambda_P$ is
  hereditary. Finally, for each $P$ we know by @th:hereditary-iff-extremal that
  $Lambda_P$ is hereditary if and only if $Lambda_P$ is extremal. This completes
  the proof.
]

Let us digress briefly to show that when $R$ contains infinitely many prime
ideals, then extremal $R$-orders are the same as maximal orders.

#theorem[
  For each $P$, $rad Lambda subset rad Lambda_P$. Further,
  $
    (rad Lambda)^n subset (rad R) Lambda, "where" n = (A : K).
  $
  If $R$ contains infinitely many prime ideals, then $rad R = 0$ and
  $rad Lambda = 0$; in this case, $Lambda$ is extremal if and only if $Lambda$
  is maximal.
] <th:radical-global-bound>

#proof[
  Given $P$, let
  $
    psi: Lambda -> overline(Lambda) = Lambda slash P Lambda tilde.equiv
    Lambda_P slash P Lambda_P.
  $
  By @th:radical-epimorphism we have $psi(rad Lambda) subset rad
  overline(Lambda)$. The chain
  $
    overline(Lambda) > rad overline(Lambda) > (rad overline(Lambda))^2 > dots.c
  $
  steadily decreases to 0; its length is at most $n$, since $overline(Lambda)$
  has dimension $n$ over $R slash P$. Therefore $(rad overline(Lambda))^n = 0$,
  and so $(rad Lambda)^n subset ker psi = P Lambda$. This implies that
  $
    {(rad Lambda)_P}^n subset P dot Lambda_P subset rad Lambda_P,
  $
  and therefore
  $
    rad Lambda subset (rad Lambda)_P subset rad Lambda_P,
  $
  as claimed.

  #source(378)Next we observe that $rad R = inter.big P$, where $P$ ranges over
  all maximal ideals of $R$. Furthermore
  $
    inter.big_P P Lambda = {inter.big P} Lambda = (rad R) Lambda,
  $
  since this holds when $Lambda = R$, and hence also when $Lambda$ is
  $R$-projective. Thence
  $
    (rad Lambda)^n subset inter.big P Lambda = (rad R) Lambda.
  $
  If $R$ contains infinitely many prime ideals, then $inter.big P = 0$ by
  §~@sec:dedekind-domains, whence $(rad Lambda)^n = 0$. But then
  $K dot rad Lambda$ is a nilpotent two-sided ideal of $A$, and is therefore 0.
  Thus $rad Lambda = 0$, and the theorem is proved.
]

We are now ready to prove that the decomposition theorem
@th:maximal-orders-components holds equally well for hereditary orders. We have

#theorem[
  Let $A$ be a separable $K$-algebra with simple components ${A_i}$, and let
  $R_i$ be the integral closure of $R$ in $K_i$. Then
  + For each hereditary $R$-order $Lambda$ in $A$, we have
    $Lambda = dsum Lambda e_i$, where the ${e_i}$ are the central idempotents of
    $A$ such that $A_i = A e_i$. Further, for each $i$, $Lambda e_i$ is a
    hereditary $R$-order in $A_i$.
  + If each $Lambda_i$ is a hereditary $R$-order in $A_i$, then $dsum Lambda_i$
    is a hereditary $R$-order in $A$.
  + An $R$-order $Lambda_i$ in $A_i$ is a hereditary $R$-order if and only if
    $Lambda_i$ is a hereditary $R_i$-order.
] <th:hereditary-center-order>

#proof[
  As in the proof of @th:maximal-orders-components and
  @th:extremal-decomposition, we need only show that $Lambda = C Lambda$, where
  $C = dsum R_i$. For each $P$, $(C Lambda)_P$ is an $R_P$-order in $A_P$ such
  that $(C Lambda)_P succ Lambda_P$. Since $Lambda_P$ is extremal, it follows
  that $(C Lambda)_P = Lambda_P$ for all $P$. Therefore $Lambda = C Lambda$, and
  the rest of the argument is straightforward.
]

We have now shown that, just as in the local case, the study of hereditary
orders can be reduced to the situation where $A$ is a central simple
$K$-algebra. Let us now examine this case in some detail. Let $Lambda$ be a
hereditary $R$-order in a central simple $K$-algebra $A$ of local capacity
$kappa_P$, local index $m_P$, at each prime $P$. This means that
$A_P tilde.equiv M_(kappa_P) (S_P)$ for some skewfield $S_P$ of index $m_P$. Let
$r_P$ denote the type of the hereditary $R_P$-order $Lambda_P$, that is,
$Lambda_P slash rad Lambda_P$ is a direct sum of $r_P$ simple components. Call
$r_P$ the _local type_ of $Lambda$ at $P$; clearly $r_P = 1$ if and only if
$Lambda_P$ is a maximal order, by @th:hereditary-maximal-overorders. Thus
$r_P = 1$ a.e., and we have previously shown that $m_P = 1$ a.e. Whether or not
$r_P = 1$ or $m_P = 1$, we know the structure of $Lambda_P$ from
§~@sec:hereditary-orders-local, and we can recover the order $Lambda$ by using
the formula
$
  Lambda = A inter {inter.big_P Lambda_P}.
$

If $Lambda'$ is a bigger $R$-order in $A$, then $Lambda_P subset (Lambda')_P$
for all $P$, with equality a.e. #source(379)Conversely, suppose that for each
$P$ we are given an $R_P$-order $X(P)$ in $A_P$, with $X(P) supset Lambda_P$ for
all $P$, and $X(P) = Lambda_P$ a.e. Then by @th:lattice-from-completions,
$
  X = A inter {inter.big_P X(P)}
$
is an $R$-order in $A$ containing $Lambda$, and $X_P = X(P)$ for all $P$. Hence
we may determine all possible orders $Lambda'$ containing $Lambda$ by
determining all possible sets of $X(P)$'s. Our main result is as follows:

#theorem[
  Let $Lambda$ be a hereditary $R$-order in the central simple $K$-algebra $A$,
  and let $S = {P_1, dots, P_m}$ be the (finite) set of prime ideals $P$ of $R$
  at which $Lambda_P$ is not a maximal order. Let $r_i$ denote the type of the
  hereditary $R_(P_i)$-order $Lambda_(P_i)$, $1 <= i <= m$.
  + There are precisely $product_(i=1)^m r_i$ distinct maximal $R$-orders in $A$
    containing $Lambda$.
  + There are precisely $product_(i=1)^m (2^(r_i) - 1)$ distinct $R$-orders in
    $A$ containing $Lambda$.
  + There are $sum_(i=1)^m r_i$ orders in $A$ which minimally
    contain#footnote[The order $Lambda'$ _minimally contains_ #idx(
        "minimally contains",
      )$Lambda$ if $Lambda' > Lambda$, but there is no order $Lambda''$ such
      that $Lambda' > Lambda'' > Lambda$.] $Lambda$.
] <th:hereditary-overorders-global>

#proof[
  All three assertions are immediate consequences of
  @th:hereditary-maximal-overorders and
  Exercise~@exc:hereditary-overorders-count. It is of interest to list the
  orders mentioned in (i) and (iii). For convenience of notation, we set
  $
    tilde(Lambda) = A inter {inter.big_(P in.not S) Lambda_P}.
  $
  We may remark that $tilde(Lambda)$ is a maximal $tilde(R)$-order in $A$, where
  $tilde(R)$ is the ring of elements of $K$ which are integral at each
  $P in.not S$.

  For each $P_i in S$, let ${Gamma_(i j) : 1 <= j <= r_i}$ be the distinct
  maximal orders in $A_(P_i)$ containing $Lambda_(P_i)$. Let
  $
    frak(M) = {(a_1, dots, a_m) : a_i in bold(Z), 1 <= a_i <= r_i "for"
      1 <= i <= m}.
  $
  For each $frak(m) = (a_1, dots, a_m) in frak(M)$, define
  $
    Gamma^frak(m) = tilde(Lambda) inter Gamma_(1, a_1) inter dots.c inter
    Gamma_(m, a_m).
  $
  Then
  $
    (Gamma^frak(m))_(P_i) = Gamma_(i, a_i), quad 1 <= i <= m.
  $
  Hence as $frak(m)$ ranges over the $product_1^m r_i$ $m$-tuples in $frak(M)$,
  the $R$-order $Gamma^frak(m)$ ranges over #source(380)all maximal orders in
  $A$ containing $Lambda$, and different $frak(m)$'s give different
  $Gamma^frak(m)$'s.

  Now put
  $
    Sigma_(i s) = inter.big_(1 <= j <= r_i, \ j != s) Gamma_(i j), quad
    1 <= s <= r_i, quad 1 <= i <= m.
  $
  Set
  $
    Omega_(i s) = tilde(Lambda) inter Sigma_(i s) inter
    {inter.big_(P in S \ P != P_i) Lambda_P}, quad 1 <= s <= r_i,
    1 <= i <= m.
  $
  Then the $sum_1^m r_i$ distinct orders ${Omega_(i s)}$ are precisely the
  orders in $A$ which minimally contain $Lambda$.

  To complete our discussion, we observe that every $R$-order in $A$ containing
  $Lambda$ is expressible as an intersection of a non-empty set of
  $Gamma^frak(m)$'s. This follows at once from
  Exercise~@exc:hereditary-overorders-count, which asserts that for
  $1 <= i <= m$, every order in $A_(P_i)$ containing $Lambda_(P_i)$ is an
  intersection of some of the orders ${Gamma_(i j) : 1 <= j <= r_i}$. It should
  be pointed out, however, that different sets of $Gamma^frak(m)$'s may yield
  the same $R$-order in $A$. For instance, suppose that $S = {P_1, P_2}$,
  $r_1 = r_2 = 2$; then
  $
    Gamma^((a, b)) = tilde(Lambda) inter Gamma_(1, a) inter Gamma_(2, b), quad
    1 <= a, b <= 2.
  $
  We have
  $
    Gamma^((1, 1)) inter Gamma^((1, 2)) inter Gamma^((2, 1)) = Lambda =
    Gamma^((1, 1)) inter Gamma^((2, 2)).
  $

  Analogously, for $1 <= i <= m$, every order in $A_(P_i)$ containing
  $Lambda_(P_i)$ is a sum of orders from ${Sigma_(i s) : 1 <= s <= r_i}$. It
  follows readily that every order $Lambda'$ properly containing $Lambda$ is
  expressible as a sum of orders chosen from the set
  ${Omega_(i s) : 1 <= s <= r_i, 1 <= i <= m}$. We leave as an exercise for the
  reader the proof that each $Lambda'$ is uniquely so expressible. Finally, we
  caution that not every sum of $Omega$'s is an order.
]

By the same type of reasoning, we have

#theorem[
  Keep the notation of @th:hereditary-overorders-global. For each $P$, let
  $
    X(P) = Lambda inter rad Lambda_P.
  $
  Then
  + For each $P$, $X(P)$ is a two-sided ideal in $Lambda$ such that
    $
      {X(P)}_Q = cases(rad Lambda_P"," & Q = P",", Lambda_Q"," & Q != P",")
    $
    where $Q$ ranges over all prime ideals of $R$.
  + #source(381)Let $I(Lambda)$ be the group of invertible two-sided
    $Lambda$-ideals in $A$ (see §~@sec:picard-groups). Then $I(Lambda)$ is the
    free abelian group with generators ${X(P) : P "arbitrary"}$.
  + There is an exact sequence
    $
      1 -> Cl R -> Picent Lambda -> product_P bold(Z) slash e_P r_P bold(Z)
      -> 1,
    $
    where for each $P$, $r_P$ is the local type of $Lambda$ at $P$, and $e_P$ is
    the ramification index of the skewfield part of $A_P$.
] <th:hereditary-two-sided-ideals>

#proof[
  Assertion (i) is clear from the discussion preceding
  @th:hereditary-overorders-global, and implies (ii) by virtue of
  Exercise~@exc:hereditary-invertible-bimodules. Furthermore, (iii) follows from
  @eq:picent-local-global and Exercise~@exc:hereditary-invertible-bimodules.
  Note that $e_P r_P = 1$ a.e.
]

Next we shall prove the global version of
Exercise~@exc:hereditary-factorization:

#theorem(title: [Jacobinski [@bib:Jacobinski1968b]])[
  Let ${frak(P)_1, dots, frak(P)_r}$ be any set of distinct prime ideals of the
  maximal $R$-order $Lambda'$ in a central simple $K$-algebra $A$. Let
  $
    frak(P)_1 dots.c frak(P)_r = L_s dots.c L_1
  $ <eq:prime-product-factorization>
  be any factorization of $product frak(P)_i$ into a proper product of integral
  ideals ${L_j}$. Set
  $
    Lambda = inter.big_(j=1)^s O_l (L_j).
  $ <eq:hereditary-from-factorization>
  Then $Lambda$ is a hereditary $R$-order contained in $Lambda'$. Conversely,
  every hereditary order arises in this way.
] <th:hereditary-global-factorization>

#proof[
  Starting with $Lambda'$ and @eq:prime-product-factorization, let $Lambda$ be
  given by @eq:hereditary-from-factorization. All of the formulas behave
  properly when we pass to completions, and for each prime ideal $P$ of $R$, we
  have
  $
    product (frak(P)_i)_P = cases(
      rad Lambda'_P & "if some" frak(P)_i supset P",",
      Lambda'_P & "otherwise."
    )
  $
  Hence for each $P$, $Lambda_P$ is hereditary by
  Exercise~@exc:hereditary-factorization. Therefore $Lambda$ is hereditary by
  virtue of @th:hereditary-iff-completions-extremal.

  Conversely, let $Lambda$ be a given hereditary order in $A$, and choose
  $Lambda' supset Lambda$, $Lambda'$ maximal. Suppose that $Lambda_P$ is maximal
  except at ${P_1, dots, P_r}$, and let $frak(P)_i$ be the prime ideal of
  $Lambda'$ containing $P_i$. By Exercise~@exc:hereditary-factorization, there
  is a factorization (for each $i$)
  $
    rad Lambda'_(P_i) = L_s^((i)) dots.c L_1^((i))
  $
  into a proper product of integral ideals, such that
  @eq:hereditary-from-factorization holds locally at $P_i$. We may assume that
  the number of factors $s$ is independent of $i$, by inserting (if need be)
  additional factors $L$ which are maximal orders. Now choose integral ideals
  $L_s, dots, L_1$ in $A$ by setting
  $
    #source(382)L_j = Lambda' inter L_j^((1)) inter dots.c inter L_j^((r)),
    quad 1 <= j <= s.
  $
  It is then an easy exercise, left to the reader, to verify that
  @eq:prime-product-factorization and @eq:hereditary-from-factorization hold
  true.
]

Turning now from abstract properties of hereditary orders, we shall give a
concrete example of a hereditary order which arises naturally in representation
theory. Let $L slash K$ be a finite galois extension (of fields), with galois
group $G$. Let $R$ be a Dedekind domain with quotient field $K$, and let $S$ be
the integral closure of $R$ in $L$. We shall assume that for each prime ideal
$P_1$ of $S$, the residue class field $S slash P_1$ is separable over
$R slash (R inter P_1)$. Call $S slash R$ _tamely ramified_ #idx(
  "tamely ramified",
)if for each $P_1$, the ramification index $e(P_1, L slash K)$ is not zero in
$R slash (R inter P_1)$. Then (see references listed in §~@sec:dedekind-domains)
$S slash R$ is tamely ramified if and only if there exists an $s_0 in S$ such
that $sum_(sigma in G) sigma(s_0) =
1$.

Now let $A = (L slash K, 1) = dsum_(sigma in G) L u_sigma$ be the trivial
crossed-product algebra given in Exercise~@exc:normal-basis-theorem. We set
$Lambda = dsum_(sigma in G) S u_sigma$, an $R$-order in the central simple
$K$-algebra $A$. Sometimes $Lambda$ is called a _twisted group ring_, #idx(
  "twisted group ring",
)#idx("group ring")and is denoted by $S compose G$.

#theorem(title: [Rosen])[
  The twisted group ring $S compose G$ is a hereditary $R$-order if and only if
  $S slash R$ is tamely ramified.
] <th:twisted-group-ring-hereditary>

#proof[
  Let $Lambda = S compose G$; we may regard $S$ as embedded in $Lambda$ via
  $s -> s dot u_1$, $s in S$, and then every left $Lambda$-module is also a left
  $S$-module. Suppose that $S slash R$ is tamely ramified, and let $s_0 in S$ be
  such that $sum_(sigma in G) sigma(s_0) = 1$. Given any left ideal $X$ of
  $Lambda$, there is an exact sequence of left $Lambda$-lattices
  $
    0 -> X' -> F stretch(->)^phi X -> 0,
  $
  with $F$ $Lambda$-free. Since $X$ is also a left $S$-lattice, and hence
  $S$-projective, the sequence is $S$-split. Thus there exists a map
  $psi in Hom_S (X, F)$ such that $phi psi = 1$ on $X$. Now set
  $
    psi' = sum_(sigma in G) u_sigma dot s_0 psi dot u_sigma^(-1).
  $
  It is easily verified that $psi' in Hom_Lambda (X, F)$, and for $x in X$ we
  have
  $
    phi psi' (x) & = sum_sigma phi u_sigma dot s_0 psi dot u_sigma^(-1) x
                   = sum_sigma u_sigma s_0 dot phi psi dot u_sigma^(-1) x \
                 & = sum_sigma u_sigma s_0 u_sigma^(-1) x
                   = {sum_sigma sigma^(-1) (s_0)} x = x.
  $
  Thus the sequence is $Lambda$-split, whence $X$ is $Lambda$-projective. This
  proves that if $S slash R$ is tamely ramified, then $Lambda$ is hereditary.

  #source(383)Conversely, suppose that $Lambda$ is hereditary, and set
  $x = sum_(sigma in G) u_sigma in Lambda$. Then the epimorphism
  $
    phi: Lambda -> Lambda x, "given by" phi(lambda) = lambda x, lambda in
    Lambda,
  $
  must be split. Hence there exists a map $psi in Hom_Lambda (Lambda x, Lambda)$
  such that $phi psi = 1$. Let us write
  $
    psi(x) = sum_(sigma in G) a_sigma u_sigma, quad a_sigma in S.
  $
  Since $u_tau dot x = x$ for each $tau in G$, we find readily that
  $a_sigma = sigma(a_1)$, $sigma in G$. But then
  $
    x = phi psi(x) = (sum_sigma a_sigma) x = (sum_sigma sigma(a_1)) x.
  $
  Therefore $sum_sigma sigma(a_1) = 1$, whence $S slash R$ is tamely ramified.
  This completes the proof. The reader should compare this with the proofs of
  @th:separable-projective-enveloping and Exercise~@exc:separable-over-ring.
]

Keeping the above terminology and notation, let us prove

#theorem(title: [Auslander–Goldman–Rim])[
  The twisted group ring $S compose G$ is a maximal $R$-order if and only if
  $S slash R$ is unramified, that is, if and only if the discriminant ideal
  $d(S slash R)$ equals $R$.
] <th:twisted-group-ring-maximal>

#proof[
  It suffices to establish the result for the case where $R$ is a discrete
  valuation ring, with maximal ideal $P$. Let $Lambda = S compose G$,
  $A = L compose G = dsum L u_sigma$ as above, and set $(L : K) = n$, so
  $A tilde.equiv M_n (K)$. Suppose that $Lambda$ is a maximal order in $A$; it
  follows from @cor:complete-local-radical and
  @th:local-maximal-two-sided-ideals that
  $
    rad Lambda = P Lambda = dsum_sigma P S u_sigma,
  $
  and that $rad Lambda$ is the unique maximal two-sided ideal of $Lambda$. If
  $d(S slash R) != R$, then we may write $P S = product P_i^(e_i)$, where the
  ${P_i}$ are distinct prime ideals of $S$, and where each $e_i > 1$. Setting
  $frak(a) = product P_i$, it is clear that
  $
    rad Lambda < dsum_sigma frak(a) u_sigma < Lambda,
  $
  and that $dsum frak(a) u_sigma$ is a two-sided ideal of $Lambda$. This gives a
  contradiction, and shows that $S slash R$ must be unramified whenever $Lambda$
  is a maximal order.

  Suppose conversely that $S slash R$ is unramified, so the inverse different
  $frak(D)^(-1) (S slash R)$ equals $S$ by @th:unramified-different. Let $Gamma$
  be any $R$-order in $A$ containing $Lambda$, and let
  $
    gamma = sum_sigma a_sigma u_sigma in Gamma, quad a_sigma in L.
  $
  Fix $tau in G$, and let $s$ range over all elements of $S$. Then
  $s gamma u_(tau^(-1)) in Gamma$, whence
  $
    tr_(A slash K) s gamma u_(tau^(-1)) in R "for all" s in S.
  $
  #source(384)By Exercise~@exc:crossed-product-trace, this gives
  $
    T_(L slash K) (s a_tau) in R quad "for all" s in S.
  $
  Therefore $a_tau in frak(D)^(-1) (S slash R) = S$ for each $tau in G$, whence
  $Gamma = Lambda$. This completes the proof of the theorem.
]

Also of interest is the following generalization of
@th:twisted-group-ring-hereditary:

#theorem(title: [Williamson, Harada])[
  Keep the notation and hypotheses introduced before
  @th:twisted-group-ring-hereditary, and let $f: G times G -> u(S)$ be a factor
  set. Let
  $
    B = (L slash K, f) = dsum_(sigma in G) L v_sigma, quad
    Gamma = dsum_(sigma in G) S v_sigma,
  $
  so $Gamma$ is an $R$-order in the central simple $K$-algebra $B$. Then $Gamma$
  is a hereditary order if and only if $S slash R$ is tamely ramified.
] <th:crossed-product-order-hereditary>

#proof[
  See Williamson [@bib:Williamson1963] and Harada [@bib:Harada1964b].
]

The remainder of this section gives Reiner's simplified version
[@bib:Reiner1974] of some results of Jacobinski [@bib:Jacobinski1971]. First of
all, we show that when $Lambda$ is hereditary, the calculation of the locally
free class group $Cl Lambda$ (defined in §~@sec:non-maximal-orders) can be
reduced to the case of maximal orders.

#theorem[
  Let $Lambda$ be a hereditary $R$-order in a separable $K$-algebra $A$, and let
  $Lambda'$ be any $R$-order in $A$ containing $Lambda$. Then there is an
  isomorphism
  $
    beta: Cl Lambda tilde.equiv Cl Lambda',
  $
  given by $beta[X] = [Lambda' times.o_Lambda X]$, $[X] in Cl Lambda$.
] <th:hereditary-class-group-iso>

#proof[
  Denote $times.o_Lambda$ by $times.o$ throughout this proof. It is easily
  checked that the stable isomorphism class of $Lambda' times.o X$ depends only
  on that of $X$, and that $(Lambda' times.o X) samegenus Lambda'$ whenever
  $X samegenus Lambda$. Thus $beta$ is well defined, and it follows readily from
  the definition of the additive structure of the class groups that $beta$ is a
  homomorphism.

  We now show that $beta$ is epic. Given any $[X'] in Cl Lambda'$, where $X'$ is
  a locally free left $Lambda'$-lattice in $A$, we may write (for each $P$)
  $
    X'_P = Lambda'_P x_P, quad x_P in u(A_P),
  $
  with $x_P = 1$ a.e. Set
  $
    X = A inter.big {inter.big_P Lambda_P x_P}.
  $
  Then $X$ is a locally free left $Lambda$-lattice in $A$ such that
  $Lambda' X = X'$. Since $Lambda' times.o X tilde.equiv Lambda' X$, it follows
  that $beta[X] = [X']$, whence $beta$ is epic.

  #source(385)Now let $cal(S) = {P_1, dots, P_n}$ be the set of all $P$'s in $R$
  such that $Lambda_P != Lambda'_P$. Given any $[X] in Cl Lambda$, we imitate
  the proof of @th:picent-to-class-group. By @th:genus-exact-sequence there
  exists a $Lambda$-exact sequence
  $
    0 -> X -> Lambda -> T -> 0,
  $ <eq:class-group-sequence>
  where $T_P = 0$ for all $P in cal(S)$. Since $Lambda'$ is projective as right
  $Lambda$-module, applying $Lambda' times.o dot$ to @eq:class-group-sequence
  yields a $Lambda'$-exact sequence
  $
    0 -> Lambda' times.o X -> Lambda' -> Lambda' times.o T -> 0.
  $ <eq:class-group-sequence-tensor>
  Now we claim that $Lambda' times.o T tilde.equiv T$ as left $Lambda$-modules.
  Indeed, both are $R$-torsion modules, and for each $P$ we have
  $
    Lambda'_P times.o T_P = T_P.
  $
  (This is clear when $P in cal(S)$, while for $P in.not cal(S)$ it holds since
  then $Lambda'_P = Lambda_P$.) Thus @eq:class-group-sequence-tensor yields a
  $Lambda$-exact sequence
  $
    0 -> Lambda' times.o X -> Lambda' -> T -> 0.
  $ <eq:class-group-sequence-reduced>
  Comparing this with @eq:class-group-sequence and using
  @exc:schanuel[Schanuel's Lemma], we obtain
  $
    X dotplus Lambda' tilde.equiv Lambda dotplus Lambda' times.o X quad
    "as left" Lambda"-modules."
  $ <eq:class-group-schanuel>

  Suppose now that $[X] in ker beta$; then $Lambda' times.o X$ is stably
  isomorphic to $Lambda'$, so there exists a free left $Lambda'$-lattice $F'$
  with
  $
    Lambda' dotplus F' tilde.equiv Lambda' times.o X dotplus F'.
  $
  Then @eq:class-group-schanuel gives
  $
    X dotplus (Lambda' dotplus F') tilde.equiv Lambda dotplus
    (Lambda' dotplus F').
  $
  But $Lambda' dotplus F'$ is a projective $Lambda$-lattice, whence
  $Lambda' dotplus F' dotplus L$ is $Lambda$-free for some $Lambda$-lattice $L$.
  Adding $L$ to both sides of the preceding equation, we deduce that $X$ is
  stably isomorphic to $Lambda$ as $Lambda$-lattices. Thus $[X] = 0$ in
  $Cl Lambda$, which shows that $beta$ is monic, and completes the proof of the
  theorem.
]

The preceding result shows, in particular, that
$Cl Lambda tilde.equiv Cl Lambda'$ for every maximal order $Lambda'$ containing
$Lambda$. Keeping the notation of @th:hereditary-center-order, let us write
$Lambda' = dsum Lambda'_i$, where $Lambda'_i$ is a maximal $R_i$-order in $A_i$.
Then
$
  Cl Lambda tilde.equiv Cl Lambda' tilde.equiv dsum Cl Lambda'_i.
$
If $K$ is an algebraic number field, or if $K$ is a function field and
$A_i = eichler(R_i)$ for each $i$, then by @th:swan-class-group we have
$
  Cl Lambda'_i tilde.equiv Cl_(A_i) R_i quad "for each" i.
$
Thus, in these cases the class group $Cl Lambda$ is known explicitly as a ray
class group of the center of $Lambda$.

Generalizing Exercise~@exc:endomorphism-ring-maximal, we prove next

#theorem[
  #source(386)Let $M$ be any nonzero left $Lambda$-lattice, where $Lambda$ is a
  hereditary $R$-order. Then $End_Lambda M$ is a hereditary $R$-order in
  $End_Lambda K M$.
] <th:hereditary-endomorphism-ring>

#proof[
  Choose a left $Lambda$-lattice $M'$ such that $M dotplus M' = Lambda^((n))$
  for some $n$, and let $Gamma = End_Lambda Lambda^((n))$. Then $Gamma$ is
  Morita equivalent to $Lambda$, whence $Gamma$ is also hereditary by
  Exercise~@exc:equivalence-preserves-hereditary. Let $e: Lambda^((n)) -> M$ be
  the projection associated with the direct sum decomposition
  $Lambda^((n)) = M dotplus M'$. Then
  $
    End_Lambda M tilde.equiv e Gamma e,
  $
  and so $End_Lambda M$ is hereditary by
  Exercise~@exc:idempotent-corner-hereditary.
]

Using this, we now show

#theorem[
  Let $Lambda$ be a hereditary $R$-order in the separable $K$-algebra $A$, where
  $K$ is a global field. Let $M$, $N$ be a pair of left $Lambda$-lattices such
  that $M samegenus N$ and $Lambda' M tilde.equiv Lambda' N$ for some order
  $Lambda'$ containing $Lambda$. If the $K$-algebra $End_A K M$ satisfies the
  Eichler condition relative to $R$ (see @def:eichler-condition-separable), then
  $M tilde.equiv N$.
] <th:hereditary-cancellation>

#proof[
  Let us set
  $
    Gamma = End_Lambda M, quad Gamma' = End_(Lambda') Lambda' M, quad
    B = End_A K M.
  $
  Then by @th:hereditary-endomorphism-ring, $Gamma$ is a hereditary $R$-order in
  the separable $K$-algebra $B$. Replacing $N$ by $alpha N$ for some nonzero
  $alpha in R$, we may assume that $N subset M$. View $M$ as a bimodule
  $lmodule(Lambda, M)_Gamma$, and set
  $
    J = Hom_Lambda (M, N).
  $
  Then $J$ is a left ideal in $Gamma$; we claim that $J samegenus Gamma$ and
  that $N = M J$.

  For each $P$, there is an isomorphism $M_P tilde.equiv N_P$, so we may write
  $
    N_P = M_P u_P, quad u_P in u(B_P).
  $
  Therefore
  $
    J_P = Hom_(Lambda_P) (M_P, N_P) = Gamma_P u_P.
  $
  This shows that $J samegenus Gamma$. It also establishes that $N = M J$, since
  the equality holds locally at all $P$. Therefore $[J]$ is an element of the
  locally free class group $Cl Gamma$.

  Now we have
  $
    Gamma' J = Hom_(Lambda') (Lambda' M, Lambda' N),
  $
  since the equality holds locally at each $P$. On the other hand,
  $Lambda' N = Lambda' M dot y$ for some $y in u(B)$, since
  $Lambda' M tilde.equiv Lambda' N$ by hypothesis. Therefore
  $Gamma' J = Gamma' y$, so that $[J]$ maps onto zero under the homomorphism
  $Cl Gamma -> Cl Gamma'$ defined #source(387)as in
  @th:hereditary-class-group-iso. Hence by @th:hereditary-class-group-iso it
  follows that $[J] = [Gamma]$. Therefore $J tilde.equiv Gamma$ by
  @eq:jacobinski-cancellation, so $J = Gamma z$ for some $z in u(B)$. Hence
  $N = M J = M z tilde.equiv M$, which completes the proof of the theorem.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $Lambda subset Lambda'$ be $R$-orders in a $K$-algebra $A$, and let $X$,
  $Y$ be left $Lambda'$-modules such that $Y$ is $R$-torsionfree. Prove that
  $
    Hom_(Lambda') (X, Y) = Hom_Lambda (X, Y).
  $
  #hint[@exc:overorder-homomorphisms][The left hand expression is clearly
    included in the right hand expression. Now let $f in Hom_Lambda (X, Y)$.
    Given $lambda' in Lambda'$, choose a nonzero $r in R$ such that
    $r lambda' in Lambda$. Then
    $
      r dot f(lambda' x) = f(r lambda' dot x) = r lambda' f(x), quad x in X,
    $
    whence $f(lambda' x) = lambda' f(x)$ for all $lambda'$, $x$ since $Y$ is
    $R$-torsionfree.]
  <hint:overorder-homomorphisms>
] <exc:overorder-homomorphisms>

#exercise[
  Let $Lambda$ be an $R$-order, $M$ and $N$ left $Lambda$-modules.
  + Let $M^* = Hom_R (M, R)$, the _dual_ of $M$. Show that $M^*$ is a right
    $Lambda$-module. Prove that each $f in Hom_Lambda (M, N)$ induces an
    $f^* in Hom_Lambda (N^*, M^*)$.
  + Show that analogous results hold when "left" and "right" are interchanged.
  + Let $phi_M: M -> M^(**)$ be the _evaluation map_ #idx(
      "evaluation map",
    )defined by
    $
      {phi_M (m)} f = f(m), quad f in M^*, quad m in M.
    $
    Show that $phi_M$ is a left $Lambda$-homomorphism.
  + Show that if $M$ is a $Lambda$-lattice, then so are $M^*$ and $M^(**)$.
    Prove that $phi_M: M tilde.equiv M^(**)$, and show that the isomorphism
    $M tilde.equiv M^(**)$ is natural, that is, for each homomorphism
    $f: M -> N$ of left $Lambda$-lattices, there is a commutative diagram
    $
      #evaluation-square
    $
    where $f$ induces $f^(**)$. #hint[@exc:lattice-duality][Use
      @th:lattices-reflexive.]
    <hint:lattice-duality>
] <exc:lattice-duality>

#exercise[
  Let $e in Gamma$ be idempotent, where $Gamma$ is a hereditary $R$-order. Show
  that $e Gamma e$ is also a hereditary $R$-order.
  #hint[@exc:idempotent-corner-hereditary][Let $L$ be any left ideal of
    $e Gamma e$; there exists a left $e Gamma e$-epimorphism
    $
      phi: (e Gamma e)^((r)) -> L, quad
      phi(alpha_1, dots, alpha_r) = sum_(i=1)^r alpha_i l_i quad "(say)," quad
      alpha_i in e Gamma e.
    $
    Extend $phi$ to a left $Gamma$-epimorphism
    $
      phi': Gamma^((r)) -> Gamma L, quad
      phi'(gamma_1, dots, gamma_r) = sum_(i=1)^r gamma_i l_i, quad
      gamma_i in Gamma,
    $
    where $Gamma L$ is a left ideal in $Gamma$. Since $Gamma$ is hereditary,
    there exists a left $Gamma$-map $psi': Gamma L -> Gamma^((r))$ splitting
    $phi'$. Let
    $
      #source(388)psi'(y) = (psi_1 (y), dots, psi_r (y)), quad y in Gamma L.
    $
    Then each $psi_i in Hom_Gamma (Gamma L, Gamma)$, and
    $psi_i (x) = e psi_i (x)$, $x in L$. Define $psi: L -> (e Gamma e)^((r))$ by
    $
      psi(x) = (psi_1 (x) e, dots, psi_r (x) e), quad x in L.
    $
    Then $psi$ is an $e Gamma e$-homomorphism, and
    $
      phi psi(x) = sum_(i=1)^r psi_i (x) e l_i = sum_(i=1)^r psi_i (x) l_i =
      phi' psi'(x) = x, quad x in L.
    $
    Thus $L$ is $e Gamma e$-projective.]
  <hint:idempotent-corner-hereditary>
] <exc:idempotent-corner-hereditary>

#exercise[
  Let $A = (L slash K, 1) = dsum_(sigma in G) L u_sigma$ be a trivial
  crossed-product algebra with $u_1 = 1$. Prove that for each $a in L$ and each
  $sigma in G$,
  $
    tr_(A slash K) a u_sigma = cases(
      T_(L slash K) a"," & sigma = 1",",
      0"," & sigma != 1"."
    )
  $
] <exc:crossed-product-trace>
