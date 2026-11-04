#import "main-defs.typ": *
#import "statements.typ": *

== Cyclic algebras <sec:cyclic-algebras>

Throughout this section let $L$ denote a finite galois extension of the field
$K$, and $E$ any extension field of $K$. The symbol $D$ will always stand for a
skewfield. Call $L$ a _cyclic_ extension of $K$ if $Gal(L slash K)$ is cyclic;
we write $Gal(L slash K) = chevron.l sigma chevron.r$ to indicate that $sigma$
is a generator for $Gal(L slash K)$. Starting with such a cyclic extension
$L slash K$, let $a$ be any element of $K^*$, and form the associative
$K$-algebra
$
  A = (L slash K, sigma, a) = dsum_(j=0)^(n-1) L u^j, quad
  u dot x = sigma(x) dot u, quad u^n = a, quad x in L,
$ <eq:cyclic-algebra>
where we identify $u^0$ with the unity element of $A$. We shall call $A$ a
_cyclic algebra_.#idx("cyclic algebra") Obviously $A$ is a crossed-product
algebra, with the elements ${u^j}$ playing the role of elements
${v_(sigma^j) : 0 <= j <= n - 1}$ such that
$
  v_(sigma^j) dot x = sigma^j (x) dot v_(sigma^j), quad 0 <= j <= n - 1, quad
  x in L.
$
Thus $A tilde.equiv (L slash K, f)$ where the factor set $f$ from
$chevron.l sigma chevron.r$ to $L^*$ is given by
$
  f_(sigma^i, sigma^j) = cases(
    1"," & i + j < n,
    a"," & i + j >= n quad 0 <= i"," j <= n - 1.
  )
$ <eq:cyclic-factor-set>
By §~@sec:crossed-product-algebras, we know that $A$ is a central simple
$K$-algebra split by $L$, and that $L$ is a self-centralizing maximal subfield
of $A$.

Conversely, if $L slash K$ is cyclic, we show that every crossed-product algebra
is a cyclic algebra.

#theorem[
  Let $G = Gal(L slash K) = chevron.l sigma chevron.r$ be cyclic of order $n$,
  and let $B = (L slash K, g)$ be a crossed-product algebra, where
  $g: G times G -> L^*$ is a normalized factor set. Then
  $
    (L slash K, g) tilde.equiv (L slash K, sigma, a), quad
    a = product_(j=0)^(n-1) g_(sigma^j, sigma) in K^*.
  $
] <th:crossed-product-cyclic>

#proof[
  #source(269)We may write
  $
    B = dsum_(j=0)^(n-1) L v_(sigma^j), quad
    v_(sigma^j) dot x = sigma^j (x) dot v_(sigma^j), quad x in L, quad
    v_(sigma^i) dot v_(sigma^j) = g_(sigma^i, sigma^j) v_(sigma^(i+j)),
  $
  for $0 <= i, j <= n - 1$. Then we obtain
  $
    & v_sigma^2 = v_sigma dot v_sigma = g_(sigma, sigma) v_(sigma^2), quad
      v_sigma^3 = (g_(sigma, sigma) v_(sigma^2)) v_sigma
      = g_(sigma, sigma) g_(sigma^2, sigma) v_(sigma^3), dots, \
    & v_sigma^n = a dot v_(sigma^n) = a.
  $
  Therefore
  $
    B = dsum_(j=0)^(n-1) L v_sigma^j, quad
    v_sigma dot x = sigma(x) dot v_sigma, quad x in L, quad v_sigma^n = a.
  $
  Since $v_sigma^n$ lies in the center of $B$, it follows that $a in K^*$, and
  the theorem is proved.
]

Using this result, we may carry over to cyclic algebras the results on
crossed-product algebras established in §~@sec:crossed-product-algebras. Let us
set
$
  N_(L slash K) (L^*) = {N_(L slash K) x : x in L^*}.
$
To begin with, we prove

#theorem[
  Let $G = Gal(L slash K) = chevron.l sigma chevron.r$ be cyclic of order $n$,
  and let $a, b in K^*$. Then
  + $(L slash K, sigma, a) tilde.equiv (L slash K, sigma^s, a^s)$ for each
    $s in bold(Z)$ such that $(s, n) = 1$.
  + $(L slash K, sigma, 1) tilde.equiv M_n (K)$.
  + $(L slash K, sigma, a) tilde.equiv (L slash K, sigma, b)$ if and only if
    $
      b = (N_(L slash K) c) a "for some" c in L^*.
    $
    In particular, $(L slash K, sigma, a) tilde.op K$ if and only if
    $a in N_(L slash K) (L^*)$.
  + $(L slash K, sigma, a) times.o_K (L slash K, sigma, b)
    tilde.op (L slash K, sigma, a b)$.
] <th:cyclic-algebra-properties>

#proof[
  Let
  $
    A = (L slash K, sigma, a) = dsum L u^j, quad
    B = (L slash K, sigma, b) = dsum L v^j,
  $ <eq:cyclic-algebras-a-b>
  where for all $x in L$,
  $
    u dot x = sigma(x) u, quad u^n = a; quad v dot x = sigma(x) v, quad v^n = b.
  $ <eq:cyclic-algebras-relations>
  If $(s, n) = 1$, then $G = chevron.l sigma^s chevron.r$ and
  $
    A = dsum_(j=0)^(n-1) L w^j, quad "where" quad w = u^s.
  $
  It is easily checked that
  $
    w dot x = sigma^s (x) dot w, quad w^n = a^s, quad x in L,
  $
  #source(270)so (i) is established.

  Assertion (ii) is a special case of @cor:crossed-product-trivial-factor-set.
  To prove (iii), note first that for any $c in L^*$ we have
  $
    A = dsum_(j=0)^(n-1) L(c u)^j,
  $
  and
  $
    c u dot x & = sigma(x) dot c u, x in L, \
      (c u)^n & = c u dot c u dots.c c u
                = c dot sigma(c) dots.c sigma^(n-1) (c) u^n \
              & = (N_(L slash K) c) a.
  $
  Then $A tilde.equiv (L slash K, sigma, a dot N c)$. Conversely, given any
  $K$-isomorphism $A tilde.equiv B$, we may assume that $A = B$ by using the
  argument in the proof of @th:crossed-product-central-simple. But then
  $v u^(-1)$ centralizes $L$, so $v = c u$ for some $c in L^*$. Therefore
  $
    b = v^n = (c u)^n = (N_(L slash K) c) a,
  $
  as claimed.

  Analogously, assertion (iv) follows from @th:crossed-product-tensor. We leave
  the details as exercise for the reader.
]

#corollary[
  Let $A = (L slash K, sigma, a)$ as above. Then $exp [A]$ is the least positive
  integer $t$ such that $a^t in N_(L slash K) (L^*)$. If $exp [A] = (L : K)$,
  then $A$ is a skewfield.
] <cor:cyclic-exponent>

#proof[
  We have $[A]^t = [(L slash K, sigma, a^t)]$ in $B(K)$. Thus $[A]^t = 1$ if and
  only if $a^t$ is a norm. For the second assertion, let $n = (L : K)$, so
  $(A : K) = n^2$. If $A tilde.equiv M_r (D)$, where $D$ has index $m$, then
  $n = m r$. But $[A]^m = 1$ in $B(K)$ by @th:exponent-divides-index, whence
  $exp [A]$ divides $m$. Hence if $exp [A] = n$, it follows that $m = n$ and
  $r = 1$. Thus $A$ is a skewfield, and the proof is completed.
]

Let us carry over to the case of cyclic algebras, two further results from
§~@sec:crossed-product-algebras.

#theorem[
  Let $G = Gal(L slash K) = chevron.l sigma chevron.r$ be cyclic of order $n$,
  and let $a in K^*$. Let $E$ be any field containing $K$, and let $E L$ be the
  composite of $E$ and $L$ in some larger field containing both $E$ and $L$. We
  may write
  $
    H = chevron.l sigma^k chevron.r = Gal(L slash L inter E)
    tilde.equiv Gal(E L slash E),
  $ <eq:cyclic-restriction-group>
  where $k$ is the least positive integer such that $sigma^k$ fixes $L inter E$.
  Then
  $
    E times.o_K (L slash K, sigma, a) tilde.op (E L slash E, sigma^k, a).
  $
] <th:cyclic-algebra-extension>

#proof[
  The isomorphism given in @eq:cyclic-restriction-group is well known from
  galois theory, #source(271)and we treat it as an identification. Let
  $
    A = (L slash K, sigma, a) = (L slash K, f)
  $
  where $f$ is normalized and is given by @eq:cyclic-factor-set. If $f'$ denotes
  the restriction of $f$ to $H times H$, then by @th:crossed-product-base-change
  we have
  $
    E times.o_K A tilde.op (E L slash E, f').
  $
  Since $E L slash E$ is a cyclic extension with galois group
  $H = chevron.l sigma^k chevron.r$, it follows from @th:crossed-product-cyclic
  that
  $
    (E L slash E, f') = (E L slash E, sigma^k, b),
  $
  where
  $
    b = product_(r=1)^(m-1) f'_(sigma^(r k), sigma^k), quad
    m = |H| = n slash k.
  $
  From @eq:cyclic-factor-set we find immediately that $b = a$, which completes
  the proof of the theorem.
]

#theorem[
  Let $K subset L subset E$, where
  $G = Gal(E slash K) = chevron.l sigma chevron.r$ is cyclic of finite order
  $t$. Let
  $
    H = Gal(E slash L), quad
    overline(G) = G slash H = Gal(L slash K)
    = chevron.l overline(sigma) chevron.r,
  $
  where $overline(sigma)$ is the image of $sigma$ in $overline(G)$. Then for any
  $a in K^*$,
  $
    (L slash K, overline(sigma), a) tilde.op (E slash K, sigma, a^((E : L))).
  $
] <th:cyclic-algebra-inflation>

#proof[
  Let $A = (L slash K, overline(sigma), a) = (L slash K, f)$, where
  $
    f_(overline(sigma)^i, overline(sigma)^j) = cases(
      1"," & i + j < n,
      a"," & i + j >= n"," quad 0 <= i"," j <= n - 1",",
    )
  $
  and where $n = (L : K)$. By @th:crossed-product-inflation, we have
  $A tilde.op (E slash K, g)$, where $g$ is the inflation of $f$. But from
  @th:crossed-product-cyclic we obtain
  $
    (E slash K, g) tilde.equiv (E slash K, sigma, b), quad
    "where" b = product_(j=0)^(t-1) g_(sigma^j, sigma).
  $
  Now $t = (E : K) = (E : L)(L : K) = s n$, where $s = (E : L)$. Further, for
  $0 <= j <= t - 1$ we have
  $
    g_(sigma^j, sigma) = f_(overline(sigma)^j, overline(sigma)) = cases(
      a"," & j = n - 1"," 2n - 1"," dots"," s n - 1",",
      1"," & "otherwise.",
    )
  $
  Therefore $b = a^s$, and the theorem is proved.
]

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  #source(272)Let $L$ be a cyclic extension of $K$. Prove that
  $
    H^2 (G, L^*) tilde.equiv B(L slash K)
    tilde.equiv K^* slash N_(L slash K) (L^*)
  $
  where $G = Gal(L slash K)$. #hint[@exc:cyclic-brauer-norm-quotient][Let
    $G = chevron.l sigma chevron.r$, and consider the map $K^* -> B(L slash K)$
    defined by $a in K^* -> [(L slash K, sigma, a)] in B(L slash K)$. Show that
    this gives an epimorphism of groups, with kernel $N_(L slash K) (L^*)$. For
    another proof, see
    Exercise~@exc:cyclic-galois-cohomology.] <hint:cyclic-brauer-norm-quotient>
] <exc:cyclic-brauer-norm-quotient>

#exercise[
  Let $A$ be a central simple $K$-algebra split by $E$, where $E$ is a cyclic
  extension of $K$ such that $(A : K) = (E : K)^2$. Prove that
  $A tilde.equiv (E slash K, sigma, a)$ for some $a in K^*$, where
  $G = Gal(E slash K) = chevron.l sigma chevron.r$.
  #hint[@exc:cyclic-algebra-from-splitting][By @cor:self-centralizing-embedding,
    we may embed $E$ in $A$ as a self-centralizing maximal subfield of $A$. The
    proof of @th:crossed-products-brauer-group then shows that $A$ is isomorphic
    to a crossed-product algebra $(E slash K, f)$, for some
    $[f] in H^2 (G, E^*)$. Finally,
    $
      (E slash K, f) tilde.equiv (E slash K, sigma, a)
    $
    for some $a in K^*$, by @th:crossed-product-cyclic.]
  <hint:cyclic-algebra-from-splitting>
] <exc:cyclic-algebra-from-splitting>

#exercise[
  Let $A'$ be a central simple $K$-algebra split by $E$, where $E$ is a finite
  cyclic extension of $K$. Prove that $A' tilde.op (E slash K, sigma, a)$ for
  some $a in K^*$, where $Gal(E slash K) = chevron.l sigma chevron.r$.
  #hint[@exc:cyclic-splitting-similar][The proof of
    @th:crossed-products-brauer-group shows that $A' tilde.op A$, for some
    central simple $K$-algebra $A$ split by $E$, such that
    $(A : K) = (E : K)^2$. Now use the preceding exercise.]
  <hint:cyclic-splitting-similar>
] <exc:cyclic-splitting-similar>

#exercise[
  Let $K = bold(Q)$, $L = bold(Q)(sqrt(2))$, and let $sigma in Gal(L slash K)$
  be defined by $sigma(sqrt(2)) = -sqrt(2)$. For $p$ an odd prime, let
  $A = (L slash K, sigma, p)$. Show that $A tilde.equiv M_2 (K)$ if 2 is a
  quadratic residue mod $p$, while $A$ is a skewfield if 2 is not a quadratic
  residue mod $p$. #hint[@exc:cyclic-algebra-sqrt2][$A$ is a skewfield if and
    only if $p in.not N(L^*)$, where $N$ means $N_(L slash K)$. Let
    $R = bold(Z)[sqrt(2)]$, and show that $R = algint {L}$. Imitating the proof
    in §~@sec:ideal-classes that the quaternion order has a euclidean algorithm,
    show that $R$ is also euclidean, and hence every ideal of $R$ is principal.

    If $p in N(L^*)$, then there exist integers $a, b, c in bold(Z)$, not all
    zero, such that $a^2 - 2b^2 = p c^2$. If $p | a$, then also $p | b$ and
    $p | c$; after cancellation and repetition of the process, we may assume
    that $p divides.not a$. Since $a^2 equiv 2b^2 (mod p)$, it follows that 2 is
    a quadratic residue mod $p$.

    Conversely, if 2 is a quadratic residue mod $p$, then there exist
    $a, b in bold(Z)$ with $p divides.not a$, $p divides.not b$, such that
    $p | (a^2 - 2b^2)$. Then $p | (a + b sqrt(2))(a - b sqrt(2))$, so $p R$ is
    not a prime ideal of $R$. Further, $p$ is unramified in $L slash K$, since
    $p$ does not divide the discriminant of $R$ over $bold(Z)$. Hence
    $p R = P_1 P_2$, where the $P_i$ are distinct ideals of $R$. Therefore
    $p bold(Z) = N_(L slash K) (P_1)$, and if $P_1 = R alpha$, then
    $p = plus.minus N alpha$. But $u = 1 + sqrt(2) in u(R)$, and $N(u) = -1$.
    Hence $p$ is either $N alpha$ or $N(u alpha)$, and so
    $p in N(L^*)$.] <hint:cyclic-algebra-sqrt2>
] <exc:cyclic-algebra-sqrt2>
