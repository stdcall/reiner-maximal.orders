#import "main-defs.typ": *
#import "statements.typ": *

== Eichler's Theorem <sec:eichler-theorem>

The following notation remains in force throughout this section:
$
      K & = "global field" \
      R & = "Dedekind domain with quotient field" K, R != K \
    K_P & = P"-adic completion of" K "at a prime" P "of" K \
  phi_P & = P"-adic valuation on" K "and" K_P #[(see §~@ss:global-fields,
            @ss:completions)] \
    R_P & = P"-adic valuation ring in" K_P", if" P = "finite prime" \
        & = {x in K_P : phi_P (x) <= 1} \
      A & = "central simple" K"-algebra," (A : K) = n^2 \
    m_P & = index [A_P] = "local index of" A "at" P \
      S & = "set of all infinite primes" P "of" K "for which" m_P > 1 \
        & = {P : P "an infinite prime of" K "ramified in" A}
$
$
  U(A) = {alpha in K^* : alpha_P > 0 "for each" P in S}.
$
(We remind the reader that the notation $K_P$, $R_P$ is different from that of
the #source(302)earlier chapters, where we had previously used $R_P$ to denote
the localization of $R$ at a prime ideal $P$, and $hat(R)_P$ for the $P$-adic
completion of $R$.)

According to the @th:hasse-schilling-maass[Hasse–Schilling–Maass Norm Theorem],
we know that
$
  nr_(A slash K) u(A) = U(A),
$
a fact which we shall use repeatedly. In this section, we shall present
Eichler's refinement of this Norm Theorem. The refinement deals with the
problem:

_Given a nonzero element $beta in R$, does there exist an element $x in A$ such
that $nr_(A slash K) x = beta$, and $x$ is integral over $R$?_

In short, we wish to characterize reduced norms of integral elements. Obviously
we must assume that $beta in U(A)$, since otherwise $beta$ cannot be a reduced
norm. We shall find that the discussion below proceeds smoothly as long as $A$
satisfies some mild restriction, called the _Eichler condition_. In the
exceptional cases, where this condition fails to hold, many of the proofs and
results given below are no longer valid. Our first task is to single out these
exceptional cases, in which the Eichler condition does not hold. We shall begin
with a number of definitions, the significance of which will not become apparent
until we are in the middle of the proof of the preliminary
@lem:eichler-approximation[Lemma] below. We shall follow the treatment given in
Swan–Evans [@bib:Swan1970].

#definition[
  Let $K$ be an algebraic number field. A central simple $K$-algebra $A$ is
  called a _totally definite quaternion algebra_ if every infinite prime $P$ of
  $K$ is ramified in $A$, and if furthermore $A_P tilde.equiv bold(H)$ for each
  such $P$. Here, $bold(H)$ denotes the quaternion skewfield over the real field
  $K_P$.
  #idx(
    "totally definite quaternion algebra",
    target: [@def:totally-definite-quaternion-algebra],
  )
] <def:totally-definite-quaternion-algebra>

We remark that no complex prime of $K$ can possibly ramify in $A$. Further, if
$A$ is a totally definite quaternion algebra, then
$
  (A : K) = (A_P : K_P) = (bold(H) : bold(R)) = 4, quad P in S.
$
Hence, $A$ is a totally definite quaternion algebra if and only if _all_ of the
following conditions hold true:
+ $(A : K) = 4$,
+ Every infinite prime of $K$ is real,
+ $A_P tilde.equiv bold(H)$ for every infinite prime $P$ of $K$.
Equivalently, these mean that $(A : K) = 4$ and that $S$ is the set of _all_
infinite primes of $K$. It is clear that the quaternion algebra over $bold(Q)$,
defined in @exm:quaternions, is totally definite.

Totally definite quaternion algebras play the role of exceptions to the theory
to be developed in this section. We shall need to find a corresponding class of
exceptions for the case where the ground field is a function field. In order to
do so, we introduce a bit of non-standard terminology. Let $K$ be any global
field, either an algebraic number field or a function field, #source(303)and let
$R$ be a Dedekind domain with quotient field $K$. Each nonzero prime ideal $P$
of $R$ gives rise to a prime of $K$, which we shall also denote by $P$, and
refer to as a "prime of $R$". Those primes of $K$, which do _not_ come from
prime ideals of $R$, will be called "non-$R$" primes of $K$. #idx(
  "non-$R$ primes",
)For example, when $K$ is an algebraic number field and $R = algint {K}$, the
ring of all algebraic integers in $K$ (see §~@sec:dedekind-domains), then the
"non-$R$" primes of $K$ are precisely the same as the infinite primes of $K$.
(For the proof of this statement, see the references listed in
§~@sec:dedekind-domains.)

It will turn out (see proof of @lem:eichler-approximation) that the central
simple $K$-algebras $A$, which are "exceptional" relative to $R$, are those
which occur in the following situations:

#condition[
  + $A$ ramifies at every "non-$R$" prime of $K$, and $(A : K) = 4$, where $K$
    is an algebraic number field, or
  + $A$ ramifies at every "non-$R$" prime of $K$, where $K$ is a function field.
] <def:exceptional-algebras>

This leads to the following definition:

#definition[
  The central simple $K$-algebra $A$ satisfies the _Eichler condition relative
  to $R$_ (notation: $A = eichler(R)$), if either
  + $K$ is an algebraic number field, and $(A : K) != 4$ if $A$ ramifies at
    every "non-$R$" prime of $K$, or
  + $K$ is a function field, and some "non-$R$" prime of $K$ does not ramify in
    $A$.
  #idx("Eichler condition", target: [@def:eichler-condition])#idx(
    "Eichler/$R$",
    target: [@def:eichler-condition],
  )
] <def:eichler-condition>

#remark[
  In particular, suppose that $K$ is an algebraic number field, and
  $R = algint {K}$. To say that "$A$ satisfies the Eichler condition relative to
  $R$" means that either $(A : K) != 4$, or else $(A : K) = 4$ but $A$ is not
  ramified at some infinite prime of $K$. In other words, in this case we have
  $A = eichler(R)$ if and only if $A$ is _not_ a totally definite quaternion
  algebra.
] <rem:eichler-condition-number-field>

The proofs of the important theorems, given later in this section, will rely
heavily on the following rather technical "approximation lemma". The proof of
this lemma requires the hypothesis that $A$ be $eichler(R)$. We have stated the
lemma in a fairly general version, since the extra generality does not make the
proof any harder, and will be needed later.

#lemma[
  We assume that
  + $A$ is a central simple $K$-algebra satisfying the Eichler condition
    relative to $R$, with $(A : K) = n^2$,
  + $S$ is the set of all infinite primes of $K$ ramified in $A$,
  + $S'$ is some non-empty finite collection of primes of $R$, including all
    those which ramify in $A$,
  + $S''$ is any finite collection (possibly empty) of primes of $R$, such that
    $S''$ is disjoint from $S'$,
  + #source(304)$beta$ is a given element of $U(A) inter R$,
  + For each $P in S' union S''$, we are given a polynomial
    $
      f_P (X) = X^n + b_(1,P) X^(n-1) + dots.c + b_(n-1,P) X + (-1)^n beta
      quad in R_P [X],
    $ <eq:approximation-local-polynomials>
    such that for each $P in S'$, $f_P (X)$ is separable and irreducible over
    $K_P$.

  Then for each $epsilon > 0$, there exists a polynomial
  $
    f(X) = X^n + a_1 X^(n-1) + dots.c + a_(n-1) X + (-1)^n beta quad in R[X],
  $ <eq:approximating-polynomial>
  satisfying all of the following conditions:
  #case-list(
    numbering: "(C1)",
    [#case[For each $P in S' union S''$,
      $
        phi_P (a_i - b_(i,P)) < epsilon, quad 1 <= i <= n - 1.
      $] <case:approximation-coefficients>],
    [#case[For each $P in S'$, $f(X)$ is irreducible over
      $K_P$.] <case:approximation-local-irreducible>],
    [#case[The polynomial $f(X)$ is separable and irreducible over
      $K$.] <case:approximation-global-irreducible>],
    [#case[For each $P in S$, $f(X)$ has no zeros in the real field
      $K_P$.] <case:approximation-no-real-zeros>],
  )
] <lem:eichler-approximation>

#proof[
  Let $epsilon > 0$ be given. After replacing $epsilon$ by a smaller positive
  number if need be, we may assume that $epsilon < 1$. We may further assume
  that the conclusion of @lem:perturbed-polynomial-irreducible[Lemma] is valid
  whenever the coefficients ${b_i}$ occurring in
  @lem:perturbed-polynomial-irreducible are subject to the condition that each
  $phi_P (b_i) < epsilon$. Our proof now splits into three cases.

  _Case 1._ $K =$ algebraic number field, $n != 2$.

  For each value of $i$, $1 <= i <= n - 1$, we are given a collection of
  elements
  $
    {b_(i,P) in R_P : P in S' union S''},
  $
  which occur as coefficients in the polynomials in
  @eq:approximation-local-polynomials. By the Strong Approximation Theorem
  @th:strong-approximation, we may approximate these elements simultaneously by
  an element $a_i in K$. Thus we may choose $a_i in K$ so that
  $
    cases(
      phi_P (a_i - b_(i,P)) < epsilon & quad "for all" P in S' union S'',
      phi_Q (a_i) <= 1 & quad "for all primes" Q "of" R "not in" S' union S''.,
    )
  $
  Since $epsilon < 1$, it follows that for each $P in S' union S''$ we have
  $a_i - b_(i,P) in R_P$, and hence also $a_i in R_P$. But also $a_i in R_Q$ for
  every prime $Q$ of $R$ not in $S' union S''$. Hence $a_i$ is integral at
  _every_ prime of $R$, and so $a_i in R$.

  We shall tentatively define $f(X)$ by formula @eq:approximating-polynomial, so
  @case:approximation-coefficients surely holds true. By virtue of the
  restriction placed on $epsilon$ at the beginning of this proof, it follows
  from @case:approximation-coefficients and
  @lem:perturbed-polynomial-irreducible that $f(X)$ is separable and irreducible
  over $K_P$, for each $P in S'$. Thus @case:approximation-local-irreducible is
  true, whence @case:approximation-global-irreducible is also true, since $S'$
  is non-empty. Unfortunately, however, the polynomial $f(X)$ may fail to
  satisfy @case:approximation-no-real-zeros.

  #source(305)If the set $S$ is empty, @case:approximation-no-real-zeros is
  vacuous, and so the lemma is established in this case. Now suppose that $S$ is
  not empty; then $n$ is even, and hence $n > 2$, since we are considering here
  the case where $n != 2$. Let $t$ be a positive rational integer, and consider
  the graph of the function $f(x) + t x^2$, where $x$ is a real variable. Since
  $n$ is even, it follows that by choosing $t$ sufficiently large, we may be
  certain that the graph lies entirely above the $x$-axis. At the same time, we
  can make $t$ divisible by a high power of each prime $P in S' union S''$.
  Therefore we may choose $t$ so that
  $
    cases(
      phi_P (t) < epsilon quad "for all" P in S' union S''",",
      f(X) + t X^2 "has no zero in the real field" K_P", for each" P in S.,
    )
  $
  Since $n > 2$, the polynomial $f(X) + t X^2$ is monic. Its coefficients
  satisfy the same inequalities @case:approximation-coefficients as do those of
  $f(X)$. Hence if we use $f(X) + t X^2$ rather than the original $f(X)$, we
  have obtained a polynomial which satisfies the conditions
  @case:approximation-coefficients–@case:approximation-no-real-zeros, as
  desired.

  _Case 2._ $K =$ algebraic number field, $n = 2$.

  Since $n = 2$, and $A = eichler(R)$ by hypothesis, it follows from
  @def:eichler-condition that there exists at least one "non-$R$" prime $P_0$ of
  $K$ at which $A$ does not ramify. Thus $P_0 in.not S union S' union S''$. We
  shall now imitate the proof given in Case 1, but this time we must use the
  Very Strong Approximation Theorem @th:very-strong-approximation, rather than
  @th:strong-approximation. For each value of $i$, where $1 <= i <= n - 1$, we
  may choose an element $a_i in K$ such that
  $
    cases(
      phi_P (a_i - b_(i,P)) < epsilon & quad "for each" P in S' union S''",",
      phi_Q (a_i) <= 1 & quad "for every prime" Q "of" R "not in"
                         S' union S''",",
      phi_P (a_i) < epsilon & quad "for every" P in S.,
    )
  $
  This application of @th:very-strong-approximation is permissible, since no
  condition has been imposed on $a_i$ at the prime $P_0$.

  As in the previous case, it follows that each $a_i in R$, and we may again
  define $f(X) in R[X]$ by formula @eq:approximating-polynomial. Just as before,
  $f(X)$ satisfies
  @case:approximation-coefficients–@case:approximation-global-irreducible.
  Furthermore, since $n = 2$, we may write
  $
    f(X) = X^2 + a_1 X + beta,
  $
  and by hypothesis $beta_P > 0$ for each $P in S$. Since
  $phi_P (a_1) < epsilon$ for each $P in S$, it is clear that if $epsilon$ is
  chosen sufficiently small, then $f(X)$ will have no zero in the real field
  $K_P$, for each $P in S$. Thus $f(X)$ satisfies
  @case:approximation-no-real-zeros, and this case is settled.

  _Case 3._ $K =$ function field.

  Since $A = eichler(R)$ by hypothesis, there exists a "non-$R$" prime $P_0$ of
  $K$ at which $A$ is not ramified. The set $S$ is empty, and
  $P_0 in.not S' union S''$, since $S' union S''$ #source(306)is a collection of
  primes of $R$. Given polynomials @eq:approximation-local-polynomials with $P$
  ranging over $S' union S''$, we use @th:very-strong-approximation to obtain an
  element $a_i in K$ such that
  $
    cases(
      phi_P (a_i - b_(i,P)) < epsilon & quad "for each" P in S' union S''",",
      phi_Q (a_i) <= 1 & quad "for every prime" Q "of" R "with"
                         Q in.not S' union S''.,
    )
  $
  As in the preceding case, this application of @th:very-strong-approximation is
  permissible, since we have imposed no condition on $a_i$ at $P_0$. We find as
  before that $a_i$ is integral at _every_ prime of $R$, and so $a_i in R$. Now
  define $f(X)$ by formula @eq:approximating-polynomial. Just as in Case 1, the
  polynomial $f(X)$ satisfies
  @case:approximation-coefficients–@case:approximation-global-irreducible, while
  @case:approximation-no-real-zeros is vacuous in this case. This completes the
  proof of the lemma.
]

As a first application of the preceding lemma, we prove the following result of
Eichler:

#theorem(major: true)[
  If $A$ satisfies the Eichler condition relative to $R$, then every
  $beta in R inter U(A)$ is the reduced norm of some element of $A$ integral
  over $R$.
  #idx("Eichler's Theorem", target: [@th:eichler-integral-norms])
] <th:eichler-integral-norms>

#proof[
  We may choose $S$ and $S'$ as in @lem:eichler-approximation, with $S''$ empty.
  Let $beta in R inter U(A)$ be given. For each $P in S'$, it follows from
  @cor:polynomial-with-given-constant-term that we may find a separable
  irreducible polynomial
  $
    f_P (X) = X^n + b_(1,P) X^(n-1) + dots.c + b_(n-1,P) X + (-1)^n beta
    quad in R_P [X],
  $
  with constant term $(-1)^n beta$. By @lem:eichler-approximation, we may then
  find a separable irreducible polynomial
  $
    f(X) = X^n + a_1 X^(n-1) + dots.c + a_(n-1) X + (-1)^n beta quad in R[X],
  $
  satisfying conditions
  @case:approximation-coefficients–@case:approximation-no-real-zeros of
  @lem:eichler-approximation. The discussion in Step 3 of the proof of
  @th:hasse-schilling-maass carries over unchanged. It shows that there exists
  an element $x in A$ such that
  $
    f(x) = 0, quad beta = nr_(A slash K) x.
  $
  But then $x$ is integral over $R$, since $f(x) = 0$, and so the theorem is
  established.
]

Before proceeding to the statement and proof of Eichler's Theorem below, we
shall recall some definitions from §~@sec:ideal-theory. A _normal ideal_ in $A$
is a full $R$-lattice $L$ in $A$ whose left and right orders are maximal
$R$-orders in $A$. If $L$ is a normal ideal with left order $Lambda$, right
order $Lambda'$, then we call $L$ a _principal_ ideal if $L = Lambda x$ for some
$x in A$. In this case,
$
  Lambda' = x^(-1) Lambda x, quad L = x Lambda',
$
so in speaking about principal ideals, it does not matter whether we deal with
the left order or the right order of $L$.

We are now ready to prove the following important result:

#theorem(major: true, title: "Eichler")[
  #source(307)Let $A$ be a central simple $K$-algebra satisfying the Eichler
  condition relative to $R$. Let $L$ be any normal ideal in $A$. Then $L$ is a
  principal ideal if and only if its reduced norm $nr_(A slash K) L$ is a
  principal ideal $R alpha$ for some $alpha in U(A)$.
  #idx("Eichler's Theorem", target: [@th:eichler])
] <th:eichler>

#proof[
  For brevity, we write $nr$ instead of $nr_(A slash K)$. Let $L$ be a normal
  ideal in $A$, and let $Lambda = O_l (L)$, a maximal $R$-order in $A$. If $L$
  is principal, then $L = Lambda x$ for some $x in u(A)$. By
  @cor:reduced-norm-generated we obtain
  $
    nr L = nr Lambda x = R dot nr x,
  $
  and $nr x in U(A)$ by @th:hasse-schilling-maass. We must prove that,
  conversely, if $nr L = R alpha$ for some $alpha in U(A)$, then $L$ is
  principal. We shall assume hereafter that $n > 1$, where $(A : K) = n^2$,
  since the result is obvious when $n = 1$.

  _Step 1._ Throughout the proof, let $d = d(Lambda slash R)$ be the
  discriminant of the maximal order $Lambda$ (see
  §~@sec:different-discriminant-global). Then $d$ is a nonzero ideal in $R$, and
  for each prime $P$ of $R$ we have (by @th:maximal-order-local-indices)
  $
    A_P tilde.op K_P quad "if and only if" quad P divides.not d.
  $

  By Exercise~@exc:conjugate-maximal-orders, there are only finitely many
  conjugacy classes of maximal $R$-orders in $A$. Let
  $
    Lambda_1 (= Lambda), Lambda_2, dots, Lambda_kappa
  $
  be a full set of representatives of these conjugacy classes. Then each maximal
  $R$-order in $A$ is of the form $u Lambda_i u^(-1)$ for some $u in u(A)$ and
  some $i$ between 1 and $kappa$. Choose once and for all a nonzero element
  $r in R$ such that $r in.not u(R)$, and
  $
    r Lambda_i subset Lambda_j, quad 1 <= i, j <= kappa.
  $ <eq:conjugacy-representatives-multiple>

  We temporarily fix a prime $P$ of $R$ such that $P divides.not r d$, and let
  $M, N$ be a pair of maximal left ideals of $Lambda$ such that
  $nr M = nr N = P$ (see @th:reduced-norm-maximal-ideal). In Step 4, we shall
  prove that necessarily $M = N theta$ for some $theta in u(Lambda)$. The
  remainder of Step 1, and the material in Steps 2 and 3, will be needed in
  Step 4.

  Let us draw some consequences from the hypothesis that $P divides.not r d$. As
  remarked above, it follows that $A_P tilde.op K_P$, so
  $A_P tilde.equiv M_n (K_P)$. Since $Lambda_P$ is a maximal $R_P$-order in
  $A_P$ by @th:completion-maximal-order, it follows from
  @th:complete-local-maximal-orders and @cor:complete-local-radical that
  $
    Lambda_P tilde.equiv M_n (R_P), quad rad Lambda_P = P dot Lambda_P.
  $
  Let us set
  $
    overline(Lambda) = Lambda slash P Lambda tilde.equiv
    Lambda_P slash P Lambda_P, quad
    overline(R) = R slash P tilde.equiv R_P slash P R_P.
  $
  Then
  $
    overline(Lambda) tilde.equiv M_n (overline(R)) tilde.equiv
    Hom_(overline(R)) (V, V),
  $ <eq:residue-order-matrix>
  #source(308)where $V$ is the vector space consisting of all $n times 1$ column
  vectors with entries in $overline(R)$. We may view $V$ as a simple left
  $overline(Lambda)$-module.

  Since $K$ is a global field, $overline(R)$ is a finite field, and hence
  $overline(Lambda)$ is a finite ring. Thus we may choose a finite set of
  elements $tau_1, dots, tau_g in Lambda$ such that
  $
    u(overline(Lambda)) = {overline(tau)_1, dots, overline(tau)_g}.
  $ <eq:residue-units>
  Let $Lambda_((P))$ denote the _localization_ of $Lambda$ at $P$. By
  @th:local-maximal-two-sided-ideals we have
  $
    rad Lambda_((P)) = Lambda_((P)) inter rad Lambda_P
    = Lambda_((P)) inter P dot Lambda_P = P dot Lambda_((P)).
  $
  Since
  $
    Lambda_((P)) slash rad Lambda_((P)) = Lambda_((P)) slash P Lambda_((P))
    tilde.equiv overline(Lambda),
  $
  it follows from Exercise~@exc:units-modulo-radical that each $tau_j$ is a unit
  in $Lambda_((P))$. Hence we may choose an element $t in R - P$ such that
  $
    t dot tau_j^(-1) in Lambda, quad j = 1, dots, g.
  $ <eq:unit-lifts-inverse>
  For later use, we note that $P divides.not t$.

  _Step 2._ We use the notation of @lem:eichler-approximation[Lemma], choosing
  $S'$ to be the set of all primes of $R$ which either ramify in $A$ or which
  divide the principal ideal $r t dot R$. (Possibly some prime divisors of
  $r t dot R$ may ramify in $A$.) Since $r in.not u(R)$, the set $S'$ is
  non-empty. We choose $S''$ to consist of the single prime ${P}$, so $S''$ is
  disjoint from $S'$.

  We are going to find a collection of polynomials ${f_Q (X) : Q in S'}$ and a
  polynomial $f_P (X)$, with certain properties. Once this is done, we shall
  approximate these polynomials by a polynomial in $R[X]$, by using
  @lem:eichler-approximation. To begin with, we claim that for each $Q in S'$,
  we may find a polynomial
  $
    f_Q (X) = X^n + b_(1,Q) X^(n-1) + dots.c + b_(n-1,Q) X + (-1)^n
    in R_Q [X],
  $
  such that
  $
    cases(
      f_Q (X) "is separable and irreducible over" K_Q",",
      f_Q (X) equiv (X - 1)^n mod Q^(n n')",",
    )
  $ <eq:local-polynomial-conditions>
  where $Q^(n')$ is the power of $Q$ occurring in $r t dot R$. (Congruence of
  polynomials means coefficientwise congruence.)

  For each prime $Q in S'$, we proceed as follows: let $W = K_Q (omega)$ be an
  unramified extension of degree $n$, with Frobenius automorphism $sigma$, where
  $omega$ is a primitive $(q^n - 1)$-th root of 1, $q = card overline(R)_Q$. Let
  $pi$ be a prime element of $R_Q$. By
  Exercise~@exc:nth-roots-near-one#ed-note[The exercise needs $n != 0$ in $R_Q$.
    If $K$ is a function field whose characteristic divides $n$,
    @eq:nth-roots-near-one fails, and one takes instead
    $f_Q (X) = minpol_(K_Q) z$ with $z = sigma(u) u^(-1)$, $u = 1 + pi^k omega$,
    $k >= n n'$. Then $N_(W slash K_Q) z = 1$ and $z equiv 1 mod pi^k R_W$.
    Moreover $z$ generates $W$: if $sigma^s$ fixed $z$ for a proper divisor $s$
    of $n$, then $w = sigma^s (u) u^(-1)$ would lie in $K_Q$, with
    $w^(n slash s) = 1$ and
    $w equiv 1 + pi^k (omega^(q^s) - omega) equiv.not 1 mod pi^(k+1)$; but $1$
    is the only root of unity in $1 + pi R_Q$ in characteristic $p$.], we may
  choose a positive integer $k >= n n'$ so large that
  $
    u equiv 1 mod pi^k R_Q ==> u = gamma^n "for some" gamma in R_Q,
    gamma equiv 1 mod pi^(n n') R_Q.
  $ <eq:nth-roots-near-one>
  Having done so, we set
  $
    g(X) = minpol_(K_Q) (1 + pi^k omega) quad in R_Q [X].
  $
  #source(309)Then $g(X)$ is a separable irreducible polynomial of degree $n$,
  and its zeros are ${1 + pi^k omega^(q^i) : 0 <= i <= n - 1}$. Therefore
  $g(X) equiv (X - 1)^n mod pi^k$. Let us write
  $
    g(X) = X^n + c_1 X^(n-1) + dots.c + c_(n-1) X + (-1)^n u.
  $
  Since $u equiv 1 mod pi^k$, it follows from @eq:nth-roots-near-one that
  $u = gamma^n$ for some $gamma in u(R_Q)$ such that
  $gamma equiv 1 mod pi^(n n')$. We now set
  $
    f_Q (X) & = gamma^(-n) g(gamma X) \
            & = X^n + gamma^(-1) c_1 X^(n-1) + dots.c + gamma^(-(n-1)) c_(n-1) X
              + (-1)^n quad in R_Q [X].
  $
  Then the polynomial $f_Q (X)$ satisfies conditions
  @eq:local-polynomial-conditions.

  Finally, we shall choose $f_P (X) in R_P [X]$ as in
  Exercise~@exc:residue-polynomial-without-zeros, so that $f_P (X)$ is a monic
  $n$th degree polynomial whose image $overline(f)_P (X)$ in $overline(R)[X]$
  has no zeros in the field $overline(R) = R slash P$, and such that $f_P (X)$
  has constant term $(-1)^n$.

  _Step 3._ We have thus constructed a set of polynomials ${f_Q (X) : Q in S'}$
  and a polynomial $f_P (X)$, all having constant term $(-1)^n$. We apply
  @lem:eichler-approximation[Lemma] with $beta = 1$, and with the sets
  $S, S', S''$ as defined in Step 2. Then there exists a separable irreducible
  polynomial
  $
    f(X) = X^n + a_1 X^(n-1) + dots.c + a_(n-1) X + (-1)^n quad in R[X],
  $
  such that $f(X)$ is coefficientwise near $f_Q (X)$ for each
  $Q in S' union S''$. Now $S'$ includes all primes of $R$ which divide
  $r t dot R$, as well as all primes of $R$ ramified in $A$. If we choose
  $epsilon$ in @lem:eichler-approximation sufficiently small, then our
  polynomial $f(X)$ will satisfy all of the following conditions:
  + $overline(f)(X)$ has no zero in $overline(R)$, where
    $overline(R) = R slash P$.
  + $f(X) equiv (X - 1)^n mod (r t)^n$.
  + $f(X)$ is irreducible over $K_Q$, for each $Q in S'$.
  + $f(X)$ has no zeros in $K_Q$, for each $Q in S$.

  Now let $x$ be a zero of $f(X)$ in some algebraic closure of $K$, and set
  $L = K(x)$. As in the proof of @th:eichler-integral-norms, we may embed $L$ in
  $A$. Then $x$ is an element of $A$ integral over $R$, and $nr x = 1$. By
  Exercise~@exc:r-unit-norm, $x^(-1)$ is also integral over $R$. We now set
  $
    y = (x - 1) slash r t quad in A.
  $
  We may write $f(X) = (X - 1)^n + (r t)^n h(X)$, where $h(X) in R[X]$ by virtue
  of (ii). Then $f(x) = 0$ implies that $y^n = -h(x) in R[x]$, and hence by
  @cor:sum-product-integral $y^n$ is integral over $R$. Therefore $y$ is also
  integral over $R$, and so there exists a maximal $R$-order in $A$ containing
  $y$. Replacing $x$ and $y$ by suitable conjugates if need be, we may assume
  that $y in Lambda_i$ for some choice of $i$ between 1 and $kappa$. Then
  $r y in Lambda$ by @eq:conjugacy-representatives-multiple, so also
  $
    x = 1 + r t y quad in Lambda.
  $
  #source(310)Since $x^(-1)$ is integral over $R$, it follows that
  $x in u(Lambda)$.

  Let us set
  $
    x_j = tau_j^(-1) x tau_j = 1 + t tau_j^(-1) dot r y dot tau_j quad
    in Lambda, quad 1 <= j <= g,
  $ <eq:unit-conjugates>
  where the fact that $x_j in Lambda$ follows from @eq:unit-lifts-inverse. Then
  $nr x_j = nr x = 1$, so each $x_j in u(Lambda)$.

  _Step 4._ We are now ready to prove the assertion: given any pair of maximal
  left ideals $M, N$ in the maximal $R$-order $Lambda$, such that
  $
    nr M = nr N = P, quad "where" P divides.not r d,
  $
  then $M = N theta$ for some $theta in u(Lambda)$. We keep the notation of
  @eq:residue-order-matrix, so $V$ is a left $overline(Lambda)$-module, and
  hence also a left $Lambda$-module. By @th:hom-isomorphisms there is a natural
  isomorphism
  $
    Hom_Lambda (Lambda, V) tilde.equiv V, quad phi -> phi(1).
  $ <eq:hom-from-order>
  Recall that the action of an element $lambda in Lambda$ on an element
  $phi in Hom_Lambda (Lambda, V)$ is given by
  $
    (lambda phi) xi = phi(xi lambda), quad xi in Lambda.
  $

  Since $nr M = P$, it follows from @cor:reduced-norm-composition-factors that
  $Lambda slash M$ is a simple left $overline(Lambda)$-module, and likewise for
  $Lambda slash N$. Hence there exist a pair of $Lambda$-exact sequences
  $
    0 -> M -> Lambda ->^phi V -> 0, quad 0 -> N -> Lambda ->^psi V -> 0,
  $
  with
  $
    M = ker phi, quad N = ker psi, quad V = Lambda phi(1) = Lambda psi(1).
  $

  _Case 1._ Suppose that the elements $phi(1)$, $psi(1)$ of the
  $overline(R)$-space $V$ are linearly dependent over $overline(R)$. Then there
  exists an $a in R - P$ such that $phi(1) = a dot psi(1)$. But then
  $(phi - a psi)(1) = 0$, so by @eq:hom-from-order we conclude that
  $phi - a psi = 0$. Therefore $ker phi = ker psi$, since $overline(a) != 0$.
  This gives $M = N$, so the assertion at the start of Step 4 is proved in this
  case.

  _Case 2._ Now suppose that $phi(1)$ and $psi(1)$ are linearly independent
  elements of the $overline(R)$-space $V$. In Step 3 we constructed an
  $x in Lambda$ such that $f(x) = 0$. Let $overline(x)_L$ denote left
  multiplication by $overline(x)$ on the $overline(Lambda)$-module $V$. Then
  $overline(f)(overline(x)_L) = 0$, whence
  $
    minpol_(overline(R)) overline(x)_L quad "divides" quad overline(f)(X).
  $
  Since $overline(f)(X)$ has no zeros in $overline(R)$, it follows that the
  $overline(R)$-linear transformation $overline(x)_L$ on $V$ has no
  characteristic root in $overline(R)$. Hence for each nonzero $v in V$, the
  vectors $v$ and $overline(x) v$ are linearly independent over $overline(R)$.
  Choose a nonzero $v in V$. Then the pair ${v, overline(x) v}$ are part of an
  $overline(R)$-basis of $V$. So also are the pair ${phi(1), psi(1)}$. Hence
  there exists an invertible linear transformation $T$ on $V$ such that
  $
    T : phi(1) -> v, quad psi(1) -> overline(x) v.
  $
  #source(311)Since $overline(Lambda) tilde.equiv Hom_(overline(R)) (V, V)$, $T$
  must be given by left multiplication by some unit
  $overline(tau)_j in u(overline(Lambda))$. Therefore
  $
    overline(tau)_j dot phi(1) = v, quad
    overline(tau)_j dot psi(1) = overline(x) v,
  $
  for some $j$ between 1 and $g$. These give
  $
    psi(1) = overline(tau)_j^(-1) overline(x) overline(tau)_j dot phi(1)
    = overline(x)_j phi(1),
  $
  where $x_j$ is defined by @eq:unit-conjugates. In view of the natural
  isomorphism @eq:hom-from-order, we obtain $psi = x_j phi$. Therefore
  $
    N = ker psi & = ker x_j phi = {xi in Lambda : (x_j phi)(xi) = 0} \
                & = {xi : phi(xi x_j) = 0} = {xi : xi x_j in M} = M x_j^(-1).
  $
  This shows that $M = N x_j$, with $x_j in u(Lambda)$, and completes the proof
  of the assertion made at the beginning of this Step.

  _Step 5._ Suppose to start with that $J$ is any left ideal in the maximal
  $R$-order $Lambda$. By @th:global-proper-product-factorization we may express
  $J$ as a proper product
  $
    J = M_1 dots.c M_k, quad M_i = "maximal integral ideal".
  $ <eq:maximal-ideal-factorization>
  Then by @th:reduced-norm-of-ideal,
  $
    nr J = (nr M_1) dots.c (nr M_k),
  $
  and each $nr M_i$ is a prime ideal of $R$ (by @th:reduced-norm-maximal-ideal).
  Hence the number of factors $k$ is uniquely determined by $nr J$. Furthermore,
  if $P$ is a prime of $R$ dividing $nr J$, then $nr M_i = P$ for some $i$,
  $1 <= i <= k$. Indeed, by @th:factorization-preassigned-order or
  Exercise~@exc:primary-factorization, we can find a factorization of $J$ in
  which $nr M_1 = P$. (This important fact may also be proved directly, as
  follows: given the ideal $J$, define
  $
    J^* = Lambda inter J_P inter inter.big_(Q != P) Lambda_Q,
  $
  where $Q$ ranges over all primes of $R$ except $P$. By
  @th:lattice-from-completions it follows that $J^*$ is a left ideal of $Lambda$
  such that
  $
    J^* supset J, quad J_P^* = J_P, quad J_Q^* = Lambda_Q quad "for all" quad
    Q != P.
  $
  Then $nr J^*$ is a power of $P$, and $J = J^* dot J^(**)$ (proper product) for
  some integral ideal $J^(**)$, by @th:to-contain-is-to-divide. When we express
  $J^*$ as a proper product of maximal integral ideals, each factor will have
  reduced norm $P$. Hence we obtain a factorization
  @eq:maximal-ideal-factorization in which $nr M_1 = P$.)

  Now let $J$ and $J'$ be any pair of left ideals of $Lambda$. We shall prove
  that
  $
    cases(reverse: #true, nr J = nr J', nr J + r d = R)
    => J' = J x "for some" x in u(A).
  $ <eq:equal-norms-ideals-equivalent>
  Let $P$ be a prime of $R$ dividing $nr J$. Then we may write
  #source(312)
  $
    J = M_1 M_2 dots.c M_k, quad J' = N_1 N_2 dots.c N_k,
  $
  where
  $
    nr M_1 = nr N_1 = P,
  $
  and where the $M$'s and $N$'s are maximal integral ideals. There are as many
  factors in $J'$ as in $J$, since $nr J' = nr J$.

  We shall establish @eq:equal-norms-ideals-equivalent by induction on $k$. By
  Step 4, we know that $M_1 = N_1 z$ for some $z in u(Lambda)$, which proves the
  result when $k = 1$. Suppose now that $k > 1$, and that the result holds (for
  all maximal orders) for products of $k - 1$ maximal integral ideals. We may
  write
  $
    J' = N_1 z dot (z^(-1) N_2 z) dots.c (z^(-1) N_k z) dot z^(-1)
    = N_1 z dot tilde(J) dot z^(-1),
  $
  where
  $
    tilde(J) = (z^(-1) N_2 z) dots.c (z^(-1) N_k z)
    = z^(-1) (N_2 dots.c N_k) z.
  $
  It is easily verified that both $tilde(J)$ and $M_2 dots.c M_k$ are left
  ideals in the maximal order $Lambda'$, where
  $
    Lambda' = O_l (M_2) & = O_r (M_1) = O_r (N_1 z) = z^(-1) O_r (N_1) z \
    & = z^(-1) O_l (N_2) z = O_l (z^(-1) N_2 z) = O_l (tilde(J)).
  $
  Furthermore,
  $
    nr tilde(J) = nr M_2 dots.c M_k, quad nr tilde(J) + r d = R.
  $
  It follows from the induction hypothesis that
  $
    tilde(J) = M_2 dots.c M_k w quad "for some" quad w in u(A).
  $
  Therefore
  $
    J' = N_1 z dot tilde(J) dot z^(-1) = M_1 M_2 dots.c M_k w z^(-1)
    = J dot w z^(-1),
  $
  which completes the proof of @eq:equal-norms-ideals-equivalent.

  _Step 6._ We are now ready to prove the theorem. Let $L$ be any normal ideal
  in $A$ such that $nr L = R alpha$, where $alpha in U(A)$, and let
  $Lambda = O_l (L)$. We must show that $L = Lambda x$ for some $x in u(A)$. By
  @cor:relatively-prime-representative we can choose $y in u(A)$ such that
  $
    L y subset Lambda, quad L y + r d Lambda = Lambda.
  $
  Set $L' = L y$, $alpha' = alpha dot nr y$. Then also $Lambda = O_l (L')$, and
  $alpha' in U(A)$ by @th:hasse-schilling-maass. If we can prove that
  $L' = Lambda z$ for some $z in u(A)$, then $L = Lambda z y^(-1)$ is also
  principal.

  Changing notation, we may hereafter assume that $L$ is a left ideal of
  $Lambda$ such that
  $
    L + r d Lambda = Lambda, quad nr L = R alpha, quad
    alpha in R inter U(A).
  $
  #source(313)Let us show that
  $
    R alpha + r d = R.
  $ <eq:norm-prime-to-rd>
  At each prime $P$ of $R$ dividing $r d$, we have
  $
    L_P + r d Lambda_P = Lambda_P
  $
  whence
  $
    L_P + P Lambda_P = Lambda_P.
  $
  By @th:nakayama[Nakayama's Lemma], this implies that $L_P = Lambda_P$.
  Therefore
  $
    (nr L)_P = nr L_P = nr Lambda_P = R_P,
  $
  which proves that $P divides.not nr L$. Thus @eq:norm-prime-to-rd is
  established.

  We next observe that since $alpha in R inter U(A)$ it follows from
  @th:eichler-integral-norms that $alpha = nr w$ for some $w in u(A)$ integral
  over $R$. If $w in Lambda$, then we obtain
  $
    nr L = nr Lambda w, quad nr L + r d = R,
  $
  and hence $L = (Lambda w) w'$ for some $w' in u(A)$, by
  @eq:equal-norms-ideals-equivalent. Thus the desired result holds when
  $w in Lambda$. The manipulations which follow are needed to take care of the
  possibility that $w in.not Lambda$. By Exercise~@exc:subring-in-maximal-order,
  the ring $R[w]$ is contained in some maximal $R$-order $Lambda'$ in $A$.
  Consider the normal ideal $(Lambda' Lambda)^(-1)$ in $A$, with the left order
  $Lambda$ and right order $Lambda'$. As in the first paragraph of this step, we
  may choose an element $z in u(A)$ such that
  $
    (Lambda' Lambda)^(-1) z subset Lambda, quad
    nr {(Lambda' Lambda)^(-1) z} + r d = R.
  $
  Let us set
  $
    M = (Lambda' Lambda)^(-1) z, quad "so" M subset Lambda, quad
    nr M + r d = R.
  $
  Then $N(M) + r d = R$ by @th:reduced-norm-of-ideal, and we have
  $
    N(M) = ord_R Lambda slash M subset M
  $
  by Exercise~@exc:order-ideal-in-ideal. Hence we may choose an element
  $gamma in N(M)$ such that
  $
    gamma R + r d = R,
  $
  and we note that $gamma in R inter M$. Therefore
  $
    gamma dot z^(-1) w z in M dot z^(-1) Lambda' z = M dot O_r (M) subset M
    subset Lambda,
  $
  and so $L' = Lambda dot gamma dot z^(-1) w z$ is a left ideal of $Lambda$.
  Also $L gamma$ is a left ideal of $Lambda$, since $gamma in R$. We have
  $
    nr L gamma & = (nr L)(nr gamma) = R alpha gamma^n, \
         nr L' & = R dot nr gamma dot nr z^(-1) w z = R gamma^n dot alpha,
  $
  #source(314)since $nr w = alpha$ by the choice of $w$. Both $alpha$ and
  $gamma$ are prime to $r d$. It follows from @eq:equal-norms-ideals-equivalent
  that $L gamma = L' x'$ for some $x' in u(A)$, whence $L = Lambda x$ for some
  $x in u(A)$, as desired. This completes the proof of Eichler's Theorem.
]

#corollary[
  Let $Lambda$ be a maximal $R$-order in $A$, where $A = eichler(R)$. Let
  $L, L'$ be left $Lambda$-ideals in $A$. Then
  $
    L' = L x "for some" x in u(A) <==>
    nr L' = alpha (nr L) "for some" alpha in U(A).
  $
] <cor:eichler-ideal-classes>

#proof[
  If $L' = L x$, then $nr L' = (nr x)(nr L)$, and $nr x in U(A)$. Conversely,
  let $nr L' = alpha (nr L)$ where $alpha in U(A)$. Let $Lambda' = O_r (L)$, and
  consider the proper product $L^(-1) dot L'$. Then
  $
    nr (L^(-1) L') = (nr L)^(-1) (nr L') = R alpha,
  $
  and $L^(-1) L'$ has left order $Lambda'$. By @th:eichler[Eichler's Theorem],
  we may write $L^(-1) L' = Lambda' x$ for some $x in u(A)$. Then
  $
    L' = L L^(-1) dot L' = L dot Lambda' x = L x,
  $
  as desired. This completes the proof.
]

Eichler's Theorem @th:eichler requires the hypothesis that $A$ be $eichler(R)$.
Without this hypothesis, Eichler [@bib:Eichler1938a] showed that the conclusion
of the theorem need not hold true. In his example, $A$ is a totally definite
quaternion algebra, and $R = algint {K}$. He proved that (for suitable choice of
$A$) there may exist a non-principal normal ideal $L$ in $A$, such that
$nr_(A slash K) L = R alpha$ for some $alpha in U(A)$.

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let $overline(R) = R slash P$ be a finite field, where $P$ is a prime of $R$,
  and let $n > 1$. Show that there exists a polynomial
  $
    f(X) = X^n + c_1 X^(n-1) + dots.c + c_(n-1) X + (-1)^n quad in R[X],
  $
  such that $overline(f)(X)$ has no zeros in $overline(R)$.
  #hint[@exc:residue-polynomial-without-zeros][Let $card overline(R) = q$. The
    number of polynomials
    $
      h(X) = X^n + c_1 X^(n-1) + dots.c + c_(n-1) X + (-1)^n quad
      in overline(R)[X]
    $
    equals $q^(n-1)$. If $h(X)$ has a zero $lambda$ in $overline(R)$, then there
    is a factorization
    $
      h(X) = (X - lambda)(X^(n-1) + dots.c + (-1)^(n-1) lambda^(-1)).
    $
    There are at most $q - 1$ choices for $lambda$, and at most $q^(n-2)$
    choices for the factor of degree $n - 1$. Thus, the number of polynomials
    $h(X)$ with a zero in $overline(R)$ is $<= (q - 1) q^(n-2)$. Hence there are
    at least
    $
      q^(n-1) - (q - 1) q^(n-2)
    $
    #source(315)polynomials $h(X) in overline(R)[X]$ with no zero in
    $overline(R)$. Pick one such $h(X)$, and choose $f(X) in R[X]$ with
    $overline(f) = h$.] <hint:residue-polynomial-without-zeros>
] <exc:residue-polynomial-without-zeros>

In Exercises~@exc:binomial-near-one–@exc:nth-roots-near-one below, $R$ is a
complete discrete valuation ring with exponential valuation $v$, prime element
$pi$, residue class field $overline(R)$.

#exercise[
  Let $n$ be a positive integer, and set $n = pi^e alpha$, $alpha in u(R)$.
  Prove that for each positive integer $r$,
  $
    (1 + pi^r X)^n = 1 + alpha pi^(r+e) X + pi^(2r) g(X),
  $
  for some $g(X) in R[X]$.
] <exc:binomial-near-one>

#exercise[
  Let $alpha in u(R)$, $beta in R$, $g(X) in R[X]$, and let $m$ be a positive
  integer. Set
  $
    h(X) = pi^m g(X) + alpha X - beta.
  $
  Show that $h(X)$ has a zero in $R$.
  #hint[@exc:linear-residue-zero][If bars denote passage to $overline(R)$, then
    $
      overline(h)(X) = overline(alpha) X - overline(beta)
      = overline(alpha) (X - overline(beta) overline(alpha)^(-1)).
    $
    By @th:hensel[Hensel's Lemma], this factorization of $overline(h)(X)$ lifts
    to a factorization $h(X) = u(X) v(X)$ in $R[X]$, with $u(X)$ monic,
    $overline(u)(X) = X - overline(beta) overline(alpha)^(-1)$.]
  <hint:linear-residue-zero>
] <exc:linear-residue-zero>

#exercise[
  Let $m, n$ be positive integers such that $n != 0$ in $R$. Show that there
  exists a positive integer $k$ such that for $u in R$,
  $
    u equiv 1 mod pi^k ==> u = gamma^n "for some" gamma in R "such that"
    gamma equiv 1 (mod pi^m).
  $
  #hint(title: [Neukirch [@bib:Neukirch1969]])[@exc:nth-roots-near-one][Let
    $n = pi^e alpha$, $alpha in u(R)$. We may assume that $m > e$. Choose
    $k >= m + e$, and set $u = 1 + pi^k beta$, $beta in R$, and
    $gamma = 1 + pi^m x$. We need only show that the equation
    $
      1 + pi^k beta = (1 + pi^m x)^n
    $
    has a solution with $x in R$. By Exercise~@exc:binomial-near-one, the
    equation becomes
    $
      1 + pi^k beta = 1 + alpha pi^(m+e) x + pi^(2m) g(x)
    $
    for some $g(X) in R[X]$. Hence we must solve
    $
      pi^(m-e) g(x) + alpha x - beta pi^(k-(m+e)) = 0, quad x in R.
    $
    Now use Exercise~@exc:linear-residue-zero.] <hint:nth-roots-near-one>
] <exc:nth-roots-near-one>
