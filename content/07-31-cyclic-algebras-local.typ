#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/07-31-cyclic-algebras-local.typ": (
  beside, composite-lattice, field-lattice, invariant-square,
  relative-brauer-diagram, relative-brauer-ladder,
)

== Cyclic algebras over local fields <sec:cyclic-algebras-local>

Throughout this section let $R$ be a complete discrete valuation ring, with
maximal ideal $P = pi R != 0$, and let $overline(R) = R slash P$. Let $K$ be the
quotient field of $R$, and $v_K$ the exponential valuation on $K$. We assume
throughout that the residue class field $overline(R)$ is finite, and set
$card overline(R) = q$.

Let $D$ be a skewfield with center $K$ and index $m$, where by definition
#source(273)$m = sqrt((D : K))$. Let us recall some details from
§~@sec:finite-residue-class-field, where we showed that each such skewfield $D$
is isomorphic to a cyclic algebra. Let $W$ be the unique unramified extension of
$K$ of degree $m$. Then $W = K(omega)$, where $omega$ is a primitive
$(q^m - 1)$th root of unity over $K$. The galois group $Gal(W slash K)$ is
cyclic of order $m$, and has as canonical generator the Frobenius automorphism
$sigma$ of $W slash K$. Recall that $sigma$ is defined by the equation
$sigma(omega) = omega^q$. We shall denote the Frobenius automorphism of the
extension $W slash K$ by $sigma_(W slash K)$; it is defined only for unramified
extensions. As in §~@ss:extensions-of-complete-fields, we use the notation $o_W$
for the valuation ring of $W$, $p_W$ for the maximal ideal of $o_W$, and
$overline(o)_W$ for the residue class field $o_W slash p_W$.

We showed in §~@sec:finite-residue-class-field that $W$ may be embedded in $D$,
and that there exists a prime element $z in D$ such that
$
  D = dsum_(j=0)^(m-1) W z^j, quad "where" z alpha z^(-1) = sigma^r (alpha),
  alpha in W, "and" z^m = pi.
$
The integer $r$ is relatively prime to the index $m$, and $D$ determines
$r mod m$ uniquely. Further, each pair $r, m$ with $(r, m) = 1$ arises from some
$D$.

In terms of the notation for cyclic algebras introduced in
§~@sec:cyclic-algebras, we have $D tilde.equiv (W slash K, sigma^r, pi)$. Choose
$s in bold(Z)$ so that $r s equiv 1 (mod m)$. Then also $(s, m) = 1$, and by
@th:cyclic-algebra-properties[(i)],
$
  D tilde.equiv (W slash K, sigma^r, pi)
  tilde.equiv (W slash K, sigma^(r s), pi^s) = (W slash K, sigma, pi^s).
$
Furthermore, we could have restricted $s$ to lie in the range $1 <= s <= m$. Let
$phi(m)$ denote the number of such integers $s$. We now prove

#theorem[
  Let $W slash K$ be an unramified extension of degree $m$, and let $sigma$ be
  the Frobenius automorphism of $W slash K$. Let ${a_s}$ be any set of $phi(m)$
  elements of $K^*$, such that the values ${v_K (a_s)}$ are relatively prime to
  $m$, and are incongruent $mod m$. Then the $phi(m)$ cyclic algebras
  ${(W slash K, sigma, a_s)}$ give a full set of non-isomorphic skewfields with
  center $K$ and index $m$.
] <th:local-skewfields-cyclic>

#proof[
  We have already seen that the cyclic algebras
  $
    {(W slash K, sigma, pi^s) : 1 <= s <= m, (s, m) = 1},
  $
  give a full set of non-isomorphic skewfields with center $K$ and index $m$.
  Now let $a in K^*$, and let
  $
    N_(W slash K) (W^*) = {N_(W slash K) (x) : x in W^*}.
  $
  We showed in @th:unramified-norm-equation that $a in N_(W slash K) (W^*)$ if
  and only if $m | v_K (a)$. On the other hand, from
  @th:cyclic-algebra-properties we know that for $a, b in K^*$, we have
  $
    (W slash K, sigma, a) tilde.equiv (W slash K, sigma, b) quad
    "if and only if" quad b a^(-1) in N_(W slash K) (W^*).
  $ <eq:unramified-cyclic-isomorphism-norm>
  #source(274)It then follows that
  $
    (W slash K, sigma, a) tilde.equiv (W slash K, sigma, b) quad
    "if and only if" quad v_K (a) equiv v_K (b) (mod m).
  $ <eq:unramified-cyclic-isomorphism-valuation>
  The assertion in the theorem is now obvious.
]

For each $[A] in B(K)$, we have denoted by $exp [A]$ the exponent of $[A]$ in
the Brauer group $B(K)$, and by $index [A]$ the index of the skewfield part of
$A$. An important consequence of the preceding discussion is the following
fundamental result:

#theorem[
  Let $D$ be a skewfield with center $K$ and index $m$. Then $m = exp [D]$.
  Hence for each $[A] in B(K)$,
  $
    exp [A] = index [A].
  $
] <th:exponent-equals-index>

#proof[
  We may take $D = (W slash K, sigma, pi^s)$ as in @th:local-skewfields-cyclic,
  with $(s, m) = 1$. Then
  $
    [D]^t = [(W slash K, sigma, pi^(s t))] in B(K)
  $
  by @th:cyclic-algebra-properties. But $(W slash K, sigma, 1) tilde.op K$ by
  @th:cyclic-algebra-properties, and so it follows that
  $(W slash K, sigma, pi^(s t)) tilde.op K$ if and only if there is a
  $K$-isomorphism
  $
    (W slash K, sigma, pi^(s t)) tilde.equiv (W slash K, sigma, 1).
  $
  But by @eq:unramified-cyclic-isomorphism-valuation, such an isomorphism exists
  if and only if $m | s t$. This proves that $[D]^t = 1$ in $B(K)$ if and only
  if $m | s t$. Since $(s, m) = 1$, it is clear that $m | s t$ if and only if
  $m | t$. This proves that $exp [D] = m$. The second assertion in the theorem
  is immediate.
]

Whether or not $(s, m) = 1$, we may still form the cyclic algebra
$A = (W slash K, sigma, pi^s)$. By @eq:unramified-cyclic-isomorphism-valuation,
the isomorphism class of $A$ depends only on $s (mod m)$, that is, on the
fraction $s slash m$ viewed as an element of the additive group
$bold(Q) slash bold(Z)$. Let us find the skewfield part of $A$; of course, we
already know that $A$ is a skewfield whenever $(s, m) = 1$.

#theorem[
  Let $W slash K$ be an unramified extension of degree $m$, with Frobenius
  automorphism $sigma$, and let $s in bold(Z)$. Write $s slash m = s' slash m'$,
  where $(s', m') = 1$. Then
  $
    (W slash K, sigma, pi^s) tilde.op (W' slash K, sigma', pi^(s'))
    = "skewfield of index" m',
  $
  where $W' slash K$ is an unramified extension of degree $m'$, with Frobenius
  automorphism $sigma'$.
] <th:unramified-cyclic-skewfield-part>

#proof[
  Let $W'$ be the subfield of $W$ fixed by $chevron.l sigma^(m') chevron.r$, so
  $W' slash K$ is unramified and $(W' : K) = m'$. The epimorphism
  $Gal(W slash K) -> Gal(W' slash K)$ carries $sigma$ onto $sigma'$ (see
  Exercise~@exc:frobenius-automorphism-properties). Setting
  $d = (W : W') = m slash m'$, it follows from @th:cyclic-algebra-inflation that
  #source(275)
  $
    (W' slash K, sigma', pi^(s')) tilde.op (W slash K, sigma, (pi^(s'))^d)
    = (W slash K, sigma, pi^s).
  $
  Since $(s', m') = 1$, we know that $(W' slash K, sigma', pi^(s'))$ is a
  skewfield, and the theorem is proved.
]

#corollary[
  Keep the above notation, and let $a in K^*$. Then the cyclic algebra
  $(W slash K, sigma, a)$ is a skewfield if and only if $(m, v_K (a)) = 1$.
] <cor:unramified-cyclic-skewfield>

#proof[
  Let $s = v_K (a)$, so
  $(W slash K, sigma, a) tilde.equiv (W slash K, sigma, pi^s)$. The result now
  follows from @th:unramified-cyclic-skewfield-part.
]

Let $W slash K$ be an unramified extension of degree $m$, with Frobenius
automorphism $sigma_(W slash K)$. Given an integer $s$, not necessarily prime to
$m$, let us form the cyclic algebra $A = (W slash K, sigma_(W slash K), pi^s)$.
We now define the _Hasse invariant_#idx("Hasse invariant")#idx(
  "invariant (Hasse)",
) of $A$, denoted by $inv A$#idx("inv $[A]$"), by the formula
$
  inv (W slash K, sigma_(W slash K), pi^s) = s slash m
  in bold(Q) slash bold(Z).
$ <eq:hasse-invariant>
The skewfield part of $A$ can be calculated by use of
@th:unramified-cyclic-skewfield-part, and it has the same Hasse invariant as
$A$. Therefore $inv A$ depends only upon the class $[A] in B(K)$, and we shall
write $inv [A]$ rather than $inv A$ hereafter. By @th:local-skewfields-cyclic,
every class in $B(K)$ is represented by some cyclic algebra
$(W slash K, sigma_(W slash K), pi^s)$ with $W slash K$ unramified, and hence
there is a well defined map
$
  inv: B(K) -> bold(Q) slash bold(Z).
$
_Caution._ Let $L slash K$ be a cyclic extension with galois group
$chevron.l sigma chevron.r$ cyclic of order $n$, and let $a in K^*$. Then the
cyclic algebra $B = (L slash K, sigma, a)$ determines a class $[B]$ in $B(K)$.
However, it is _not_ necessarily true that $inv [B] = v_K (a) slash n$. Indeed,
even when $L slash K$ is unramified, the formula is valid only when $sigma$
equals the Frobenius automorphism $sigma_(L slash K)$. Further, in the ramified
case the Frobenius automorphism $sigma_(L slash K)$ is not even defined. In
order to compute $inv [B]$ when $L slash K$ is ramified, we must first write
$B tilde.op (W slash K, sigma_(W slash K), pi^s) = A$ for some unramified
extension $W slash K$, and then we have $inv [B] = inv [A] = s slash m$.

We are now ready to prove the important result:

#theorem[
  $inv: B(K) tilde.equiv bold(Q) slash bold(Z)$.
] <th:hasse-invariant-isomorphism>

#proof[
  The map $inv$ is epic, since each element of $bold(Q) slash bold(Z)$ is of the
  form $s slash m$, with $(s, m) = 1$, $m >= 1$. Now let $[A] in B(K)$ be
  represented by the cyclic algebra
  $
    A = (W slash K, sigma, pi^s), "where" W slash K "is unramified,"
    sigma = sigma_(W slash K), "and" (W : K) = m.
  $
  Then $inv [A] = s slash m in bold(Q) slash bold(Z)$, so $inv [A] = 0$ if and
  only if $m | s$, that is, if and only if $A tilde.op K$. This proves that
  $inv$ is monic.

  #source(276)Finally, given $[A], [B] in B(K)$, we may choose $W slash K$
  unramified so that
  $
    A = (W slash K, sigma, pi^s), quad B = (W slash K, sigma, pi^t), quad
    sigma = sigma_(W slash K).
  $
  Then
  $
    A times.o_K B tilde.op (W slash K, sigma, pi^(s+t))
  $
  by @th:cyclic-algebra-properties. Therefore
  $
    inv [A][B] = inv [A] + inv [B],
  $
  which completes the proof that $inv$ is an isomorphism of groups.
]

We shall denote $inv$ by $inv_K$ when we need to specify the underlying field
$K$. Our next result, of great importance, describes the effect on $inv$ of a
change in ground fields.

#theorem[
  Let $E$ be any finite extension of $K$. The following diagram commutes:
  $
    #invariant-square
  $
  where the horizontal maps are isomorphisms, and where the second vertical map
  is defined to be multiplication by $(E : K)$.
] <th:hasse-invariant-extension>

#proof[
  Let $A = (W slash K, sigma, pi^s)$ represent a class $[A] in B(K)$, where
  $W slash K$ is unramified, $sigma = sigma_(W slash K)$, and $(W : K) = m$. We
  may view $W$ and $E$ as embedded in some algebraic closure of $K$, and then we
  may form their intersection $F = E inter W$ and their composite $E W$. If $k$
  is the least positive integer such that $sigma^k$ fixes $F$, then $F slash K$
  is unramified and $(F : K) = k$. By @th:cyclic-algebra-extension we have
  $
    E times.o_K A tilde.op (E W slash E, sigma^k, pi^s),
  $
  so it remains for us to compute the Hasse invariant of the right hand
  expression.

  As in §~@sec:completions-and-valuations, let $o_E$ denote the valuation ring
  of $E$, $overline(o)_E$ its residue class field, and $v_E$ the exponential
  valuation on $E$. Then
  $
    (E : K) = e f, quad e = e(E slash K), quad f = f(E slash K), quad
    v_E = e dot v_K "on" K.
  $
  Note that $m = (W : K) = (overline(o)_W : overline(o)_K)$. Let us put
  $
    d = (m, f), quad m = d m', quad f = d f',
  $
  where $(m', f') = 1$.

  Since $d$ divides both $m$ and $f$, there is a field
  $tilde(o) subset overline(o)_W inter overline(o)_E$ with
  $(tilde(o) : overline(o)_K) = d$. By @cor:inertia-field it follows that there
  is a field $tilde(F) subset W inter E = F$, such that
  #source(277)
  $
    tilde(F) slash K "is unramified," quad
    (tilde(F) : K) = (tilde(o) : overline(o)_K) = d, quad
    tilde(o) = overline(o)_(tilde(F)).
  $
  On the other hand, the field $overline(o)_F$ is contained in both
  $overline(o)_W$ and $overline(o)_E$, whence $(overline(o)_F : overline(o)_K)$
  divides both $m$ and $f$, hence divides $d$. But
  $
    k = (F : K) = (overline(o)_F : overline(o)_K), quad
    d = (tilde(F) : K), quad F supset tilde(F).
  $
  Since we have just shown that $k | d$, it follows that $F = tilde(F)$ and
  $k = d$. Consequently we obtain
  $
    f(E slash F) = f(E slash K) slash f(F slash K) = f slash d = f'.
  $
  Diagrammatically, we have
  #beside(composite-lattice)[
    $
      & Gal(E W slash E) tilde.equiv Gal(W slash F)
        = chevron.l sigma^k chevron.r, \
      & m' = (W : F) = (E W : E).
    $
  ]

  Now let $tau$ be the Frobenius automorphism of $E W slash E$, and view
  $sigma^k$ as element of $Gal(E W slash E)$. By
  Exercise~@exc:frobenius-automorphism-properties[(iv)] we have
  $
    tau = (sigma^k)^(f(E slash F)) = sigma^(k f').
  $
  But $(f', m') = 1$, and $m' = (E W : E)$, so by
  @th:cyclic-algebra-properties[(i)] we obtain
  $
    (E W slash E, sigma^k, pi^s)
    tilde.equiv (E W slash E, sigma^(k f'), pi^(s f')).
  $
  Therefore
  $
    E times.o_K A tilde.op (E W slash E, tau, pi^(s f')),
  $
  and so
  $
    inv_E [E times.o_K A]
    & = v_E (pi^(s f')) slash m' = s f' dot v_E (pi) slash m' \
    & = s f' e slash m' = s f e slash m = (E : K) dot inv [A].
  $
  This completes the proof of the theorem.
]

#corollary(major: true)[
  Let $D$ be a skewfield with center $K$ and index $m$, and let $E$ be any
  finite extension of $K$. Then $E$ splits $D$ if and only if $m | (E : K)$.
] <cor:local-splitting-degree>

#proof[
  Consider the element $[D] in B(K)$; then $inv [D] = s slash m$ for some $s$
  relatively prime to $m$. Clearly $E$ splits $D$ if and only if
  $inv_E [E times.o_K D] = 0$. #source(278)On the other hand,
  $
    inv_E [E times.o_K D] = (E : K) dot s slash m.
  $
  Since $(s, m) = 1$, we conclude that $inv_E [E times.o_K D] = 0$ if and only
  if $m | (E : K)$. This gives the desired result.
]

As a consequence of the preceding corollary, we obtain the following amazing
result:

#theorem[
  Let $D$ be a skewfield with center $K$ and index $m$. Then every irreducible
  $m$-th degree equation over $K$ has a solution in $D$.
] <th:local-skewfield-roots>

#proof[
  Let $f(X) in K[X]$ be irreducible, and of degree $m$. Let $E = K(a)$, where
  $minpol_K a = f(X)$. Then $(E : K) = m$, so $E$ splits $D$ by
  @cor:local-splitting-degree. It follows from @cor:self-centralizing-embedding
  that there is a $K$-embedding of $E$ into $D$. The image of $a$ is then an
  element of $D$ which satisfies the equation $f(X) = 0$.
]

We conclude with a further consequence of @th:hasse-invariant-isomorphism and
@th:hasse-invariant-extension.

#theorem(major: true)[
  Let $E slash K$ be any finite extension of degree $n$. Then $B(E slash K)$ is
  cyclic of order $n$.
] <th:local-relative-brauer-cyclic>

#proof[
  By definition, $B(E slash K)$ consists of all classes $[A] in B(K)$ which are
  split by $E$. Hence by @th:hasse-invariant-extension there is a commutative
  diagram
  $
    #relative-brauer-diagram
  $
  where the top row is exact, the bottom map is given by multiplication by $n$,
  and the vertical maps are isomorphisms. It follows at once that $B(E slash K)$
  is isomorphic to the kernel of the bottom map, that is,
  $
    B(E slash K) tilde.equiv 1/n bold(Z) slash bold(Z).
  $
  This completes the proof.
]

#corollary[
  If $(E : K) = n$, then
  $
    B(E slash K) = {[A] in B(K) : [A]^n = 1}.
  $
] <cor:local-relative-brauer-group>

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#source(279)The hypotheses and notation given at the beginning of this section
remain in force throughout these exercises.

#exercise[
  Consider the diagram
  $
    #field-lattice
  $
  in which all of the fields indicated are finite extensions of $K$. We assume
  that $W slash K$ is unramified, and denote its Frobenius automorphism by
  $sigma_(W slash K)$.
  + Prove that $sigma_(W slash K) in Gal(W slash K)$ is characterized by the
    condition
    $
      sigma_(W slash K) (x) equiv x^(card overline(o)_K) (mod p_W), quad
      x in o_W.
    $
  + Prove that $F slash K$ is unramified, and that the epimorphism
    $
      Gal(W slash K) -> Gal(F slash K)
    $
    carries $sigma_(W slash K)$ onto $sigma_(F slash K)$. If $k$ is the least
    positive integer such that
    $
      (sigma_(W slash K))^k in Gal(W slash F),
    $
    prove that
    $
      (F : K) = k, quad sigma_(W slash F) = (sigma_(W slash K))^k.
    $
  + Let $E dot W$ be the composite of $E$ and $W$ in some extension field of
    $K$. Show that $E W slash E$ is an unramified extension, and that
    $
      sigma_(E W slash E) ("restricted to" W)
      = (sigma_(W slash F))^(f(E slash F))
      = (sigma_(W slash K)^k)^(f(E slash F)),
    $
    where $f(E slash F) = (overline(o)_E : overline(o)_F)$.
  + When $F = E inter W$, there is an isomorphism
    $
      Psi: Gal(W slash F) tilde.equiv Gal(E W slash E),
    $
    obtained by extending each $F$-automorphism of $W$ to an $E$-automorphism of
    $E W$. For each $sigma in Gal(E W slash E)$, $Psi^(-1) sigma$ is just the
    restriction of $sigma$ to $W$. Deduce from (iii) that
    $
      sigma_(E W slash E) = Psi{(sigma_(W slash K)^k)^(f(E slash F))}.
    $
  #hint[@exc:frobenius-automorphism-properties][The results are straightforward
    consequences of the definition of the Frobenius automorphism of an
    unramified extension. Detailed proofs are available in the references listed
    at the beginning of §~@sec:dedekind-domains.]
  <hint:frobenius-automorphism-properties>
] <exc:frobenius-automorphism-properties>

#exercise[
  Let $L slash K$ be a cyclic extension of degree $n$, possibly ramified. Prove
  that $K^* slash N_(L slash K) (L^*)$ is cyclic of order $n$.
  #hint[@exc:local-norm-quotient-cyclic][Use
    Exercise~@exc:cyclic-brauer-norm-quotient and
    @th:local-relative-brauer-cyclic[Theorem].]
  <hint:local-norm-quotient-cyclic>
] <exc:local-norm-quotient-cyclic>

#exercise[
  Let $K subset E subset F$, where $(F : E) = m$, $(E : K) = n$. We make no
  assumptions as to ramification, nor do we assume that the extensions are
  galois extensions. Prove that the sequence of groups
  $
    1 -> B(E slash K) stretch(-->)_"incl" B(F slash K)
    stretch(-->)_(E times.o_K dot) B(F slash E) -> 1
  $
  #source(280)is exact, where _incl._ is the inclusion map.
  #hint[@exc:relative-brauer-exact-sequence][Consider the diagram
    $
      #relative-brauer-ladder
    $
    Show that the left hand square commutes (use
    @th:local-relative-brauer-cyclic), and so does the right hand square (use
    @th:hasse-invariant-extension). Then use exactness of the bottom row.]
  <hint:relative-brauer-exact-sequence>
] <exc:relative-brauer-exact-sequence>

#exercise[
  Let $L slash K$ be any cyclic extension, with galois group
  $chevron.l sigma chevron.r$. Prove that for $s in bold(Z)$,
  $
    inv_K [(L slash K, sigma, pi^s)]
    = s dot inv_K [(L slash K, sigma, pi)].
  $
] <exc:invariant-of-power>

#exercise[
  Let $bold(R)$ be the real field, $bold(C)$ the complex field,
  $
    bold(R)^+ = {x in bold(R) : x >= 0}.
  $
  Let $N: bold(C) -> bold(R)$ be the norm map. Prove that
  $N(bold(C)) = bold(R)^+$.
] <exc:complex-norms>

#exercise[
  Let $D$ be a skewfield with center $bold(C)$, such that $(D : bold(C))$ is
  finite. Prove that $D = bold(C)$.
  #hint[@exc:skewfield-over-algebraically-closed][Let $a in D$, and set
    $minpol_bold(C) (a) = f(X) in bold(C)[X]$. Then there exist elements
    ${alpha_i}$ in $bold(C)$ such that $f(X) = product (X - alpha_i)$. Since
    $product (a - alpha_i) = 0$, and $D$ is a skewfield, some factor
    $a - alpha_i$ must be zero.] <hint:skewfield-over-algebraically-closed>
] <exc:skewfield-over-algebraically-closed>

#exercise[
  Let $sigma$ be complex conjugation on $bold(C)$, and let $bold(H)$ be the
  cyclic algebra
  $
    bold(H) = (bold(C) slash bold(R), sigma, -1).
  $
  Prove that $bold(H)$ is the skewfield consisting of quaternions over
  $bold(R)$.#idx("quaternion skewfield") #hint[@exc:real-quaternions-cyclic][The
    least positive integer $t$ such that
    $(-1)^t in N_(bold(C) slash bold(R)) (bold(C)^*)$ is given by $t = 2$. Thus
    $bold(H)$ is a skewfield, by @cor:cyclic-exponent. As in the example
    following @cor:crossed-product-trivial-factor-set, we have
    $
      bold(H) tilde.equiv bold(R) plus.o bold(R) i plus.o bold(R) j
      plus.o bold(R) k,
    $
    where
    $
      i^2 = j^2 = k^2 = -1, quad i j = -j i = k.
    $] <hint:real-quaternions-cyclic>
] <exc:real-quaternions-cyclic>

#exercise[
  Prove that if $D$ is a skewfield whose center contains $bold(R)$, and for
  which $(D : bold(R))$ is finite, then $D = bold(C)$, $bold(R)$, or $bold(H)$.
  #hint[@exc:real-skewfields][If the center of $D$ is $bold(C)$, then
    $D = bold(C)$ by Exercise~@exc:skewfield-over-algebraically-closed. Suppose
    now that $D$ has center $bold(R)$, and that the index of $D$ is $m$, where
    $m > 1$. Then $D$ has a maximal subfield $E$, with $(E : bold(R)) = m$.
    Hence $E = bold(C)$, $m = 2$, and by §~@sec:cyclic-algebras we may write
    $
      D tilde.equiv (bold(C) slash bold(R), sigma, a), quad a in bold(R)^*,
    $
    where $sigma$ is complex conjugation. The isomorphism class of the cyclic
    algebra $A = (bold(C) slash bold(R), sigma, a)$ depends only on the coset of
    $a$ in $bold(R)^* slash N(bold(C)^*)$, where $N$ is the norm map from
    $bold(C)$ to $bold(R)$. By Exercise~@exc:complex-norms, it follows that $A$
    is determined up to isomorphism by the sign of the element $a$. But we have
    $
      (bold(C) slash bold(R), sigma, 1) tilde.equiv M_2 (bold(R)), quad
      (bold(C) slash bold(R), sigma, -1) = bold(H),
    $
    so the result follows.] <hint:real-skewfields>
] <exc:real-skewfields>

#exercise[
  Prove that $[bold(H)] in B(bold(R))$ has exponent 2.
] <exc:quaternions-exponent-two>
