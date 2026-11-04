#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/common.typ": ladder
#import "diagrams/01-02-homological-algebra.typ": (
  flat-summand, induced-maps, projective-lifting, square, triangle,
)

== Homological algebra <sec:homological-algebra>

#source(17)This section contains a brief review of several topics from
homological algebra. In most cases, proofs will be omitted. For details, we
refer the reader to standard references such as Cartan–Eilenberg
[@bib:Cartan1956], Hilton–Stammbach [@bib:Hilton1971], Jans [@bib:Jans1964],
Northcott [@bib:Northcott1960], Rotman [@bib:Rotman1970]. We shall use the same
terminology and notation as the last of these references.

#heading(level: 3)[Modules: homomorphisms, pullbacks, pushouts, tensor products,
  chain conditions] <ss:modules>

Throughout this section let $Lambda$ be a ring, not necessarily commutative,
having a unity element 1. All $Lambda$-modules are left $Lambda$-modules, unless
otherwise specified, and each $Lambda$-module $M$ is assumed _unital_ (that is,
$1 dot m = m$, $m in M$). Given a pair of $Lambda$-modules $L$ and $M$, denote
by $Hom_Lambda (L, M)$ the additive group consisting of all
$Lambda$-homomorphisms from $L$ into $M$. For each $phi in Hom_Lambda (L, M)$,
let $ker phi$ denote the _kernel_ of $phi$, $im phi$ the _image_ of $phi$, and
$cok phi$ the _cokernel_ of $phi$, that is, #idx("ker (kernel)")#idx(
  "im (image)",
)#idx("cok (cokernel)")
$
  cok phi = M slash phi(L).
$
When there is no danger of confusion, we shall write $Hom$ instead of
$Hom_Lambda$.

A sequence of $Lambda$-modules and $Lambda$-homomorphisms
$
  X_1 stretch(-->)^(f_1) X_2 stretch(-->)^(f_2) X_3 --> dots.c
  stretch(-->)^(f_(n-1)) X_n
$ <eq:sequence-of-modules>
is _exact_ at $X_i$ if $ker f_i = im f_(i-1)$. The sequence is _exact_ if it is
exact at each place, that is,
#idx("exact sequence")
$
  ker f_i = im f_(i-1), quad 2 <= i <= n - 1.
$
An exact sequence of $Lambda$-modules and $Lambda$-homomorphisms will sometimes
be called a _$Lambda$-exact sequence_.

A _short exact sequence_ is an exact sequence of the form
#idx("short exact sequence")
$
  0 --> L stretch(-->)^f M stretch(-->)^g N --> 0.
$ <eq:short-exact-sequence>
Exactness of @eq:short-exact-sequence is equivalent to the following three
conditions: $f$ is monic, $ker g = im f$, $g$ is epic. In this case, $g$ induces
an isomorphism $M slash f(L) tilde.equiv N$.

The short exact sequence @eq:short-exact-sequence is _split_ if $f(L)$ is a
direct summand of $M$. This is equivalent to either of the following:
#idx("split (sequence)")
+ There exists an $h in Hom_Lambda (M, L)$ such that $h dot f = 1_L$, where
  $1_L$ denotes the identity map on $L$.
+ There exists an $h' in Hom_Lambda (N, M)$ such that $g dot h' = 1_N$.

A diagram of $Lambda$-modules and $Lambda$-homomorphisms
#source(18)
$
  #triangle($L$, $M$, $N$, $f$, $g$, $h$)
$
is _commutative_ if $g dot f = h$. The same terminology applies to more
complicated diagrams.
#idx("commutative diagram")

Given a $Lambda$-homomorphism $f: L -> M$, and an arbitrary $Lambda$-module $X$,
there are two maps induced by $f$, namely
$
  cases(
    f_*: Hom(X, L) -> Hom(X, M)",",
    f^*: Hom(M, X) -> Hom(L, X).
  )
$ <eq:induced-maps>
These are defined by the commutative diagrams
$
  #induced-maps
$
Note that $Hom_Lambda (X, L)$, $Hom_Lambda (X, M)$, etc., are additive groups
(but not usually $Lambda$-modules), and the maps $f_*$, $f^*$ are additive
homomorphisms.

The map $f_*$ goes "in the same direction" as $f$, namely from $L$ to $M$. Since
$f_*$ arises from a change in the second variable occurring in $Hom$, we say
that $Hom$ is _covariant_ in the second variable.
#idx("covariant (functor)")

Similarly, $f^*$ goes "in the opposite direction" from $f$. Since $f^*$ arises
from a change in the first variable in $Hom$, we call $Hom$ _contravariant_ in
the first variable.
#idx("contravariant (functor)")

If $f: L -> M$ and $g: M -> N$ are $Lambda$-homomorphisms, then
$
  (g f)_* = g_* dot f_*, quad (g f)^* = f^* dot g^*.
$ <eq:composition-induced-maps>
(Contravariance reverses order of composition of mappings!)

The concepts of covariance and contravariance are extremely useful in working
with modules. Thus, for example, let $Delta$ be another ring, and let
$M = lmodule(Lambda, M)_Delta$ be a _$(Lambda, Delta)$-bimodule_, that is, $M$
is a left $Lambda$-module and right $Delta$-module, with the actions of $Lambda$
and $Delta$ on $M$ commuting:
#idx("bimodule")
$
  (lambda m) delta = lambda (m delta).
$
If $L = lmodule(Lambda, L)$ is a left $Lambda$-module, then $Hom_Lambda (M, L)$
can be given the structure of a $Delta$-module, because of the bimodule
structure on $M$. Since $M$ is a _right_ $Delta$-module, and $M$ appears in a
_contravariant_ position, it is automatically true that $Hom_Lambda (M, L)$ must
be a _left_ $Delta$-module. To be explicit, for each $f in Hom_Lambda (M, L)$
and each $delta in Delta$, we define
$
  (delta f) m = f(m delta).
$
This is the only "natural" definition, and it must use the fact that $M$ is a
right #source(19)$Delta$-module. The hypothesis that $M$ be a
$(Lambda, Delta)$-bimodule is needed to verify that $delta f$ is again a
$Lambda$-homomorphism. Analogously, $Hom_Lambda (L, M)$ can be made into a
_right_ $Delta$-module, by setting
$
  (g delta) x = g(x) dot delta, quad g in Hom_Lambda (L, M), quad
  delta in Delta, quad x in L.
$

We state without proof a theorem describing the effect of applying
$Hom_Lambda (X, dot)$ or $Hom_Lambda (dot, Y)$ to $Lambda$-exact sequences.

#theorem[
  + For each $Lambda$-module $X$ and each $Lambda$-exact sequence
    $
      0 --> L stretch(-->)^f M stretch(-->)^g N,
    $
    the sequence of additive groups
    $
      0 --> Hom_Lambda (X, L) stretch(-->)^(f_*) Hom_Lambda (X, M)
      stretch(-->)^(g_*) Hom_Lambda (X, N)
    $
    is exact.
  + For each $Lambda$-module $Y$ and each $Lambda$-exact sequence
    $
      L stretch(-->)^f M stretch(-->)^g N --> 0,
    $
    the sequence of additive groups
    $
      0 --> Hom_Lambda (N, Y) stretch(-->)^(g^*) Hom_Lambda (M, Y)
      stretch(-->)^(f^*) Hom_Lambda (L, Y)
    $
    is exact.
] <th:hom-left-exact>

It is sometimes convenient to use the concepts of pushouts and pullbacks of
pairs of maps. Given a pair of $Lambda$-homomorphisms $f_i: A -> M_i$,
$i = 1, 2$, we define a $Lambda$-module $X$, called the _pushout_ of the pair
$(f_1, f_2)$, by the formula
#idx("pushout (diagram)")
$
  X = (M_1 dotplus M_2) slash {(f_1 a, -f_2 a) : a in A}.
$
Thus $X$ is obtained from the external direct sum $M_1 dotplus M_2$ by
identifying the image of $A$ in $M_1$ with the image of $A$ in $M_2$. There is a
commutative diagram (called a _pushout diagram_ or _fibre sum_)
$
  #square($A$, $M_1$, $M_2$, $X$, $f_1$, $f_2$, $g_1$, $g_2$)
$
where $g_i$ is defined by composition: $M_i -> M_1 dotplus M_2 -> X$,
$i = 1, 2$. The pushout $X$ is characterized up to isomorphism by a "universal
mapping property", as follows: given any commutative diagram of $Lambda$-modules
and $Lambda$-homomorphisms
#source(20)
$
  #square($A$, $M_1$, $M_2$, $X';$, $f_1$, $f_2$, $g'_1$, $g'_2$)
$
there is a unique $Lambda$-homomorphism $psi: X -> X'$ such that
$psi g_i = g'_i$, $i = 1, 2$.

Dually, given $Lambda$-homomorphisms $f_i: M_i -> B$, $i = 1, 2$, we can form
their _pullback_ (or _fibre product_)
#idx("fibre product")
$
  Y = {(m_1, m_2) in M_1 dotplus M_2 : f_1 m_1 = f_2 m_2}.
$
There is a commutative _pullback diagram_
#idx("pullback (diagram)")
$
  #square($Y$, $M_1$, $M_2$, $B,$, $g_1$, $g_2$, $f_1$, $f_2$)
$
where $g_i (m_1, m_2) = m_i$, $i = 1, 2$. The pullback $Y$ is also characterized
by a universal mapping property: given any commutative diagram
$
  #square($Y'$, $M_1$, $M_2$, $B,$, $g'_1$, $g'_2$, $f_1$, $f_2$)
$
there is a unique $phi: Y' -> Y$ such that $g'_i = g_i phi$, $i = 1, 2$.

Next, we recall some facts about tensor products (see Curtis–Reiner
[@bib:Curtis1962, §~12], for example). Given a right $Lambda$-module $L$ and a
left $Lambda$-module $M$ (notation: $L_Lambda$, $lmodule(Lambda, M)$), we may
form their tensor product $L times.o_Lambda M$. This is an additive group, but
not usually a $Lambda$-module. The tensor product $L times.o_Lambda M$ is
covariant in each variable: given $Lambda$-homomorphisms $f: L_1 -> L_2$,
$g: M_1 -> M_2$, there is an additive homomorphism
$
  f times.o g: L_1 times.o_Lambda M_1 -> L_2 times.o_Lambda M_2.
$
Consequently, if $Delta$ is another ring with unity element, and if
$lmodule(Delta, L)_Lambda$ is a bimodule, then for each $lmodule(Lambda, M)$ we
can make $L times.o_Lambda M$ into a left $Delta$-module in a natural way. The
action of an element $delta in Delta$ on $L times.o_Lambda M$ is given by
$
  delta (sum l_i times.o m_i) = sum delta l_i times.o m_i, quad
  l_i in L, quad m_i in M.
$
In particular, if $Lambda$ is commutative and $L$, $M$ are viewed as two-sided
$Lambda$-modules, then $L times.o_Lambda M$ is also a $Lambda$-module.

The effect of applying $X times.o_Lambda dot$ or $dot times.o_Lambda Y$ to exact
sequences is described in the following result, stated without proof:

#source(21)
#theorem[
  + Given a right $Lambda$-module $X$ and an exact sequence of left
    $Lambda$-modules $L -> M -> N -> 0$, there is an exact sequence of additive
    groups
    $
      X times.o_Lambda L -> X times.o_Lambda M -> X times.o_Lambda N -> 0.
    $
  + Given $lmodule(Lambda, Y)$ and an exact sequence of right $Lambda$-modules
    $A -> B -> C -> 0$, there is an exact sequence of additive groups
    $
      A times.o_Lambda Y -> B times.o_Lambda Y -> C times.o_Lambda Y -> 0.
    $
] <th:tensor-right-exact>

Next we list a number of natural isomorphisms involving $Hom$ and $times.o$. In
most cases there is no difficulty in writing down explicitly the maps which
yield these isomorphisms, and we shall leave this task to the reader. It will
also be clear from the context whether the modules which occur are left
$Lambda$-modules or right $Lambda$-modules, and we shall suppress such
information in some of the statements below.

#theorem[
  + Given $lmodule(Lambda, M)$, there is a left $Lambda$-isomorphism
    $
      Hom_Lambda (Lambda, M) tilde.equiv M,
    $
    obtained by mapping each $f in Hom_Lambda (Lambda, M)$ onto $f(1)$. The left
    $Lambda$-structure of $Hom_Lambda (Lambda, M)$ arises from the
    $Lambda$-$Lambda$-bimodule structure of $Lambda$.
  + For each index set $I$,
    $
      Hom_Lambda (dsum_(i in I) M_i, N)
      & tilde.equiv product_(i in I) Hom_Lambda (M_i, N), \
      Hom_Lambda (M, product_(i in I) N_i)
      & tilde.equiv product_(i in I) Hom_Lambda (M, N_i).
    $
    Choosing $I$ to be the finite set ${1, dots, k}$, it follows as special
    cases of these formulas that $Hom$ commutes with finite direct sums in
    either variable:
    $
      Hom_Lambda (dsum_(i=1)^k M_i, N) & tilde.equiv
                                         dsum_(i=1)^k Hom_Lambda (M_i, N), \
      Hom_Lambda (M, dsum_(i=1)^k N_i) & tilde.equiv
                                         dsum_(i=1)^k Hom_Lambda (M, N_i).
    $
] <th:hom-isomorphisms>

#theorem[
  + Given $lmodule(Lambda, M)$, there is a left $Lambda$-isomorphism
    $
      Lambda times.o_Lambda M tilde.equiv M,
    $
    obtained by mapping $sum lambda_i times.o m_i in Lambda times.o_Lambda M$
    onto $sum lambda_i m_i in M$. The left $Lambda$-structure of
    $Lambda times.o_Lambda M$ arises from the $Lambda$-$Lambda$-bimodule
    structure of $Lambda$.
  + Tensor product commutes with direct sums:
    #source(22)
    $
      (dsum_(i in I) M_i) times.o_Lambda N
      & tilde.equiv dsum_(i in I) (M_i times.o_Lambda N), \
      M times.o_Lambda (dsum_(i in I) N_i)
      & tilde.equiv dsum_(i in I) (M times.o_Lambda N_i),
    $
    for any index set $I$.
] <th:tensor-isomorphisms>

Finally we give some results on chain conditions. A $Lambda$-module $M$ is
_noetherian_ if the submodules of $M$ satisfy the ascending chain condition
(A.C.C.), that is, if every ascending chain of submodules terminates. The ring
$Lambda$ is _left noetherian_ if the left ideals of $Lambda$ satisfy the A.C.C.
The following result is used repeatedly (see Curtis–Reiner [@bib:Curtis1962,
§~11]): #idx("noetherian")#idx("A.C.C.")

#theorem[
  For a ring $Lambda$, the following are equivalent:
  + $Lambda$ is left noetherian.
  + Every finitely generated left $Lambda$-module is noetherian.
  + Every submodule of a finitely generated left $Lambda$-module is finitely
    generated.
  + Every nonempty collection of submodules of a finitely generated left
    $Lambda$-module contains a maximal element.
] <th:noetherian-equivalences>

#corollary[
  Let $R$ be a commutative noetherian ring, and let $Lambda$ be an $R$-algebra
  which is finitely generated as $R$-module. Then $Lambda$ is left and right
  noetherian as a ring.
] <cor:algebra-over-noetherian-ring>

#proof[
  Every left ideal of $Lambda$ is an $R$-submodule of the finitely generated
  $R$-module $Lambda$. Since $R$ is noetherian, it follows from
  @th:noetherian-equivalences[(ii)] that the $R$-submodules of $Lambda$ satisfy
  the A.C.C. Hence the left ideals of $Lambda$ satisfy the A.C.C., so $Lambda$
  is left noetherian. Likewise $Lambda$ is right noetherian.
]

Next, a $Lambda$-module $M$ is _artinian_ if its submodules satisfy the
descending chain condition (D.C.C.), that is, if every descending chain of
submodules terminates. The ring $Lambda$ is _left artinian_ if its left ideals
satisfy the D.C.C. We have (see Curtis–Reiner [@bib:Curtis1962, §~11]) #idx(
  "artinian",
)#idx("D.C.C.")

#theorem[
  The following statements are equivalent:
  + $Lambda$ is left artinian.
  + Every finitely generated left $Lambda$-module is artinian.
  + Every nonempty collection of submodules of a finitely generated
    $Lambda$-module contains a minimal element.
] <th:artinian-equivalences>

Just as in the preceding discussion, we obtain

#corollary[
  Let $R$ be a commutative artinian ring, and let $Lambda$ be an #source(
    23,
  )$R$-algebra which is finitely generated as $R$-module. Then $Lambda$ is left
  and right artinian as a ring.
] <cor:algebra-over-artinian-ring>

=== Functors and categories <ss:functors-and-categories>

In order to simplify the remaining discussion of homological algebra, and also
for later use in the chapter on Morita equivalence, it is convenient to
introduce some of the concepts of category theory. For simplicity, we shall
restrict our attention to categories of modules. (For a more detailed account of
category theory, see MacLane [@bib:MacLane1963].) If $Lambda$ is a ring with
unity element, let $cal(M)_Lambda$ denote the category of right
$Lambda$-modules. The _objects_ of $cal(M)_Lambda$ are right $Lambda$-modules,
and for each $L, M in cal(M)_Lambda$, there is a set of _morphisms_ (or _maps_)
from $L$ to $M$, namely $Hom_Lambda (L, M)$.
#idx("morphism")

Let $cal(A)$ be a category with objects $A, A', dots$, and $cal(B)$ a category
with objects $B, B', dots$ A (covariant) _functor_ $F: cal(A) -> cal(B)$ carries
each $A in cal(A)$ onto an object $F A in cal(B)$, and carries each
$alpha in Hom_(cal(A)) (A, A')$ onto a map
$F alpha in Hom_(cal(B)) (F A, F A')$, in such a way as to preserve identity
maps and compositions. We assume always that our functors are _additive_, that
is, $F(alpha_1 + alpha_2) = F alpha_1 + F alpha_2$. A _contravariant_ functor
$F: cal(A) -> cal(B)$ carries $A in cal(A)$ onto $F A in cal(B)$, and carries
each $alpha in Hom_(cal(A)) (A, A')$ onto $F alpha in Hom_(cal(B)) (F A', F A)$;
such an $F$ reverses composition of maps. #idx("functor")#idx(
  "additive functor",
)#idx("contravariant (functor)")#idx("covariant (functor)")

A covariant functor $F$ is _right exact_ if it carries each exact sequence
$A_1 -> A_2 -> A_3 -> 0$ in $cal(A)$ onto an exact sequence
$F A_1 -> F A_2 -> F A_3 -> 0$ in $cal(B)$. For example, if $Ab$ denotes the
category of abelian groups, and $X_Lambda$ is some fixed right $Lambda$-module,
there is a functor $F: lmodule(Lambda, cal(M)) -> Ab$, given by
$M -> X times.o_Lambda M$, and $alpha -> 1 times.o alpha$. We often write
$F = X times.o_Lambda dot$. @th:tensor-right-exact[Theorem] is just the
assertion that $F$ is a right exact functor. #idx("right exact")#idx(
  "exact (right, left)",
)

On the other hand, let $lmodule(Lambda, X)$ be a fixed left $Lambda$-module, and
define $F: lmodule(Lambda, cal(M)) -> Ab$ by $M -> Hom_Lambda (X, M)$,
$M in lmodule(Lambda, cal(M))$. We must also describe the action of $F$ on maps;
if $alpha in Hom_Lambda (M, M')$, we set $F alpha = alpha_*$ (see
@eq:induced-maps). Then $F$ is covariant, and @th:hom-left-exact asserts that
$F$ is a _left exact_ functor. We often write $F = Hom_Lambda (X, dot)$.
#idx("left exact")

One can also define right- or left-exactness of contravariant functors. We shall
not give the definition here, but remark only that the functor
$F: lmodule(Lambda, cal(M)) -> Ab$, given by $F = Hom_Lambda (dot, X)$, is a
contravariant functor which is left exact (by @th:hom-left-exact).

A functor $F: cal(A) -> cal(B)$ is _exact_ if $F$ is both left and right exact.
We state without proof:
#idx("exact functor")

#theorem[
  Let $F: cal(A) -> cal(B)$ be a covariant functor. The following conditions are
  equivalent:
  + $F$ is an exact functor.
  + $F$ preserves exactness of short exact sequences, that is, if #source(
      24,
    )$0 -> A_1 -> A_2 -> A_3 -> 0$ is an $cal(A)$-exact sequence, then
    $0 -> F A_1 -> F A_2 -> F A_3 -> 0$ is an exact sequence in $cal(B)$.
  + $F$ preserves exactness of sequences, that is, if $A' -> A -> A''$ is
    $cal(A)$-exact, then $F A' -> F A -> F A''$ is $cal(B)$-exact.
] <th:exact-functor-criteria>

=== Projective and flat modules <ss:projective-and-flat-modules>

A (left) $Lambda$-module $F$ is said to have a _free_ $Lambda$-basis
${x_alpha}$, where $alpha$ ranges over some index set, if there exist elements
$x_alpha in F$ such that each $x in F$ is expressible as a finite sum
$x = sum c_alpha x_alpha$ with uniquely determined coefficients
$c_alpha in Lambda$. Such modules $F$ are called _free_ $Lambda$-modules.
Equivalently, $F$ is free if and only if $F$ is isomorphic to a direct sum of
copies of the left $Lambda$-module $lmodule(Lambda, Lambda)$. #idx(
  "free basis",
)#idx("free module")

Every $Lambda$-module $M$ is a homomorphic image of some free module $F$.
Indeed, choose any set of elements $m_alpha in M$ such that
$M = sum Lambda m_alpha$, and let $F$ be free with basis ${x_alpha}$; then
define an epimorphism $phi: F -> M$ by letting $phi(x_alpha) = m_alpha$. Note
that if $M$ is finitely generated as $Lambda$-module, then $F$ may be chosen
free with a finite basis.

A _projective_ $Lambda$-module is a direct summand of a free module. For
example, if $Lambda = J_1 plus.o J_2$, where each $J_i$ is a left ideal of
$Lambda$, then $J_1$ and $J_2$ are projective left $Lambda$-modules. Obviously,
every free module is projective. Let ${M_i}$ be any family of $Lambda$-modules.
It is clear from the definition of projectivity that $dsum M_i$ is projective if
and only if each $M_i$ is projective. As we shall see, projective modules play a
basic role in homological algebra, and in other areas of algebra as well. We
state without proof (see references listed at the beginning of
§~@sec:homological-algebra):
#idx("projective module")

#theorem[
  Let $P$ be any $Lambda$-module. The following statements are equivalent:
  + $P$ is projective.
  + Every short exact sequence $0 -> X -> Y -> P -> 0$ must split.
  + Given any diagram with exact bottom row
    $
      #projective-lifting
    $
    there exists a $Lambda$-homomorphism $h$ such that $f = g h$.
  + Given any epimorphism $g: X -> Y$, the induced map
    $
      g_*: Hom_Lambda (P, X) -> Hom_Lambda (P, Y)
    $
    is also an epimorphism.
  + #source(25)$Hom_Lambda (P, dot)$ is an exact functor.
] <th:projective-criteria>

#remark(numbered: false)[
  There is a concept of _injective_ modules, dual to that of projective modules:
  a $Lambda$-module $L$ is _injective_ if every short exact sequence
  $0 -> L -> X -> Y -> 0$ is necessarily split. The analogue of
  @th:projective-criteria holds true. We shall seldom need to use injective
  modules in this book.
  #idx("injective module")
]

A right $Lambda$-module $X$ is _flat_ if $X times.o_Lambda dot$ preserves
exactness, that is, if for every exact sequence of left $Lambda$-modules
#idx("flat")
$
  L stretch(->)^f M stretch(->)^g N,
$
the sequence of additive groups
$
  X times.o_Lambda L stretch(-->)^(1 times.o f) X times.o_Lambda M
  stretch(-->)^(1 times.o g) X times.o_Lambda N
$
is also exact. We may rephrase this definition as follows: the module $X_Lambda$
determines a covariant functor $F: lmodule(Lambda, cal(M)) -> Ab$ as in
§~@ss:functors-and-categories, by setting $F(M) = X times.o_Lambda M$,
$M in lmodule(Lambda, cal(M))$. Then $X$ is flat if and only if $F$ is an exact
functor. We have already remarked in @th:tensor-right-exact that $F$ is always
right exact, and the only question to be decided is whether $F$ is also left
exact. Hence we have

#theorem[
  A module $X_Lambda$ is flat if and only if $X times.o_Lambda dot$ preserves
  monomorphisms, that is, for each monomorphism $f: L -> M$ of left
  $Lambda$-modules, the additive homomorphism
  $
    1 times.o f: X times.o_Lambda L -> X times.o_Lambda M
  $
  is also monic.
] <th:flat-criterion>

#corollary[
  Every projective module is flat.
] <cor:projective-flat>

#proof[
  The right $Lambda$-module $Lambda_Lambda$ is flat, because of the isomorphism
  given in @th:tensor-isomorphisms[(i)]. Since tensor product commutes with
  direct sum (see @th:tensor-isomorphisms), it follows that every free right
  $Lambda$-module is flat. Now let $X_Lambda$ be projective; then $X$ is a
  direct summand of some free right $Lambda$-module $F$, and we may write
  $F = X plus.o X'$ for some module $X'$. Let $f: L -> M$ be a monomorphism of
  left $Lambda$-modules. Then there is a commutative diagram
  $
    #flat-summand
  $
  Since $F$ is flat, $1_F times.o f$ is monic. Hence also $1_X times.o f$ is
  monic, and therefore $X$ is flat, as claimed.
]

#remark[
  The technique of the preceding proof can be applied to many #source(26)similar
  situations. In order to prove certain types of theorems about projective
  modules, one first treats the case of a free module on one generator, then the
  case of an arbitrary free module, and finally the case of projective modules.
  Of course, one needs to know that the functors which occur commute with the
  operation of forming direct sums. In many arguments, it suffices to restrict
  attention to finite direct sums.
] <rem:free-then-projective>

#remark[
  We shall show in §~@ss:flatness that every ring of quotients $R'$ of a
  commutative ring $R$ is a flat $R$-module. From @th:flat-criterion it then
  follows that for each inclusion of $R$-modules $L subset M$, there is an
  inclusion of $R'$-modules $R' times.o_R L subset R' times.o_R M$. Further,
  there is an $R'$-isomorphism
  $
    R' times.o_R (M slash L) tilde.equiv
    (R' times.o_R M) slash (R' times.o_R L),
  $
  a result to be used repeatedly.
] <rem:ring-of-quotients-flat>

Next we note

#theorem[
  A right $Lambda$-module $X$ is flat if every finitely generated submodule of
  $X$ is flat.
] <th:flat-finitely-generated-submodules>

#proof[
  See Rotman [@bib:Rotman1970, Corollary~3.31]. The converse of this theorem is
  false.
]

Using this, we prove (see also Exercise~@exc:completion-faithfully-flat):

#theorem[
  Let $R$ be a principal ideal domain. Then every torsionfree#footnote[An
    $R$-module $X$ is _torsionfree_ iff for each nonzero $x in X$ and each
    nonzero $r in R$, also $r x != 0$.] $R$-module is flat.
  #idx("torsionfree")
] <th:torsionfree-flat-pid>

#proof[
  Submodules of torsionfree modules are also torsionfree. Hence by
  @th:flat-finitely-generated-submodules, it suffices to prove that every
  finitely generated torsionfree $R$-module $X$ is flat. But by the Structure
  Theorem for modules over principal ideal domains (see Curtis–Reiner
  [@bib:Curtis1962, §~16]), each such $X$ is $R$-free. Hence $X$ is $R$-flat, by
  @cor:projective-flat, and the theorem is proved.
]

As a matter of fact, the converse of @th:torsionfree-flat-pid also holds: if $X$
is a flat $R$-module, then $X$ must be torsionfree (see Rotman [@bib:Rotman1970,
Exercise~3.11]).

A flat right $Lambda$-module $X$ is _faithfully flat_ if for each left
$Lambda$-module $L$, the equality $X times.o_Lambda L = 0$ implies that $L = 0$.
To test for faithful flatness, we may use the result:
#idx("faithfully flat")

#theorem[
  Let $X_Lambda$ be flat. The following statements are equivalent:
  + $X$ is faithfully flat.
  + A sequence of left $Lambda$-modules is exact if and only if it becomes exact
    after applying $X times.o_Lambda dot$ to it.
  + #source(27)For each left $Lambda$-homomorphism $f: L -> M$, the map
    $1 times.o f: X times.o_Lambda L -> X times.o_Lambda M$ is the zero map if
    and only if $f = 0$.
  + For each maximal left ideal $frak(m)$ of $Lambda$, we have $X != X frak(m)$.
] <th:faithfully-flat-criteria>

#proof[
  See Bourbaki [@bib:Bourbaki1961a, §~3, no.~1].
]

#corollary(note: [See also Exercises~@exc:completion-faithfully-flat,
  @exc:dedekind-completion-flat.])[
  Let $R$ be a principal ideal domain, $P$ a prime ideal of $R$, and $R^*$ the
  $P$-adic completion of $R$. Then $R^*$ is a flat $R$-module. If $R$ is a
  discrete valuation ring, then $R^*$ is faithfully flat as $R$-module.
] <cor:completion-flat>

#proof[
  (See §~@ss:completions for the relevant definitions.) There is an embedding
  $R -> R^*$ which makes $R^*$ into an $R$-module. Then $R^*$ is
  $R$-torsionfree, since $R^*$ is also an integral domain. Therefore $R^*$ is
  $R$-flat, by @th:torsionfree-flat-pid.

  Now suppose that $R$ is a discrete valuation ring, with unique maximal ideal
  $P$. Then $P R^*$ is the unique maximal ideal of $R^*$, so $R^* != P R^*$. It
  follows from @th:faithfully-flat-criteria[(iv)] that $R^*$ is faithfully flat,
  as claimed.
]

#corollary[
  Let $R^*$ be the completion of a discrete valuation ring $R$. For each left
  $R$-module $M$ let $M^* = R^* times.o_R M$, a left $R^*$-module. Then $R^*$ is
  faithfully flat as $R$-module. This means
  + For every exact sequence of $R$-modules
    $
      0 -> L -> M -> N -> 0,
    $
    the sequence of $R^*$-modules
    $
      0 -> L^* -> M^* -> N^* -> 0
    $
    is also exact, and
  + $L^* = 0$ if and only if $L = 0$.
] <cor:completion-faithfully-flat>

As a matter of fact, the results of @cor:completion-faithfully-flat hold in a
more general situation: given any commutative noetherian ring $R$ having a
unique maximal ideal $P$, we may form the $P$-adic completion $R^*$ of $R$. It
is then true that $R^*$ is a faithfully flat $R$-module (see Bourbaki
[@bib:Bourbaki1961b]).

=== Extensions of modules <ss:extensions-of-modules>

We shall first give an informal discussion of $Ext_Lambda^1 (N, L)$ in terms of
equivalence classes of extensions of a left $Lambda$-module $N$ by a left
$Lambda$-module $L$. Then we shall define $Ext_Lambda^n$ in terms of projective
resolutions, and shall list standard properties of $Ext$. In what follows, all
modules are left $Lambda$-modules, and we shall write $Hom$ instead of
$Hom_Lambda$ for convenience.

#source(28)A $Lambda$-exact sequence
$
  0 -> L stretch(->)^f X stretch(->)^g N -> 0
$ <eq:extension>
is called an _extension_ of $N$ by $L$; sometimes we refer to the module $X$
itself as such an extension. Another extension $0 -> L -> X' -> N -> 0$ is
_equivalent_ to that in @eq:extension if there exists a $Lambda$-isomorphism
$theta$ making the following diagram commutative: #idx(
  "extension of modules",
)#idx("equivalence", "of extensions")
$
  #ladder(
    ($0$, $L$, $X$, $N$, $0$),
    ($0$, $L$, $X'$, $N$, $0,$),
    (none, $1_L$, $theta$, $1_N$, none),
  )
$
where $1_L$, $1_N$ are identity maps. This defines an equivalence relation among
extensions of $N$ by $L$. _Caution_: it may happen that $X tilde.equiv X'$ even
though the extensions are inequivalent.

We shall introduce an additive group $Ext_Lambda^1 (N, L)$ whose elements are in
one-to-one correspondence with the equivalence classes of extensions of $N$ by
$L$. To begin with, choose an epimorphism $phi: P -> N$, where $P$ is
$Lambda$-projective (we could even choose $P$ $Lambda$-free, if desired), and
let $K = ker phi$. This gives a $Lambda$-exact sequence
$
  0 -> K stretch(->)^psi P stretch(->)^phi N -> 0,
$
with $psi$ the inclusion map. Keeping the $Lambda$-module $L$ fixed, let $sigma$
range over the elements of $Hom(K, L)$. For each such $sigma$, let $X_sigma$
denote the pushout of the pair of maps $psi: K -> P$, $sigma: K -> L$ (see
§~@ss:modules). It follows readily from Exercise~@exc:pushout-exact-rows that
there is a commutative diagram with exact rows:
$
  #ladder(
    ($0$, $K$, $P$, $N$, $0$),
    ($0$, $L$, $X_sigma$, $N$, $0.$),
    (none, $sigma$, [], $1_N$, none),
    top-maps: ([], $psi$, $phi$, []),
    down-side: right,
  )
$
Thus each $sigma in Hom(K, L)$ yields an extension $X_sigma$ of $N$ by $L$.

The map $psi$ induces a map $psi^*: Hom(P, L) -> Hom(K, L)$. For each
$tau in im psi^*$, it is easily verified that the extension $X_(sigma + tau)$ is
equivalent to $X_sigma$. Hence, each element of the factor group
$Hom(K, L) slash im psi^*$ determines an equivalence class of extensions of $N$
by $L$. Conversely, we show that every class can be obtained in this manner.
Given any extension @eq:extension, it follows from the fact that $P$ is
projective that there exists a homomorphism $rho$ making the diagram below
commutative:
$
  #ladder(
    ($0$, $K$, $P$, $N$, $0$),
    ($0$, $L$, $X$, $N$, $0.$),
    (none, none, $rho$, $1_N$, none),
    top-maps: ([], $psi$, $phi$, []),
    bottom-maps: ([], $f$, $g$, []),
  )
$
#source(29)Clearly $rho$ induces a map $sigma: K -> L$, and it can be verified
that the extension $X$ is equivalent to $X_sigma$. One also checks that the
class of $X$ uniquely determines $sigma$ modulo the image of $psi^*$. Hence
there is a bijection between the set of equivalence classes of extensions of $N$
by $L$, and the additive group given by
$
  Ext_Lambda^1 (N, L) = Hom(K, L) slash psi^* {Hom(P, L)}.
$ <eq:ext-one>
The split extension corresponds to 0 in this group. (One can define an additive
structure on the set of equivalence classes of extensions, by using "Baer sums",
as in Rotman [@bib:Rotman1970]. In that case, the above bijection is in fact an
additive homomorphism, and the expression @eq:ext-one defines $Ext$ up to
isomorphism, regardless of the choice of $P$ and $phi$. We shall not go into
further details of this matter, however, but pass at once to the definition of
$Ext^n$ by means of projective resolutions.)

Given a left $Lambda$-module $N$, choose an epimorphism $phi_0: F_0 -> N$, with
$F_0$ free. Then choose an epimorphism $phi_1: F_1 -> ker phi_0$, with $F_1$
free, and so on. This yields a _free resolution_ of $N$, that is, a
$Lambda$-exact sequence
#idx("free resolution")
$
  dots.c -> F_2 stretch(->)^(phi_2) F_1 stretch(->)^(phi_1) F_0
  stretch(->)^(phi_0) N -> 0
$
in which each $F_i$ is $Lambda$-free. It is often more convenient to use a more
general concept: a _projective resolution_ of $N$ is an exact sequence
#idx("projective resolution")
$
  dots.c -> P_2 stretch(->)^(phi_2) P_1 stretch(->)^(phi_1) P_0
  stretch(->)^(phi_0) N -> 0
$ <eq:projective-resolution>
in which each $P_i$ is $Lambda$-projective. (If it happens that $ker phi_m$ is
projective for some $m$, then the process of forming such a resolution can be
terminated, giving a finite resolution
$
  0 -> ker phi_m -> P_m -> P_(m-1) -> dots.c -> P_0 -> N -> 0.
$
In this case, we say that $N$ has _finite homological dimension_.)
#idx("homological dimension")

Given a projective resolution @eq:projective-resolution, the subsequence
$
  bold(P): dots.c -> P_2 stretch(->)^(phi_2) P_1 stretch(->)^(phi_1) P_0 -> 0
$
is called a _deleted projective resolution_ of $N$; it is an exact sequence
except possibly at $P_0$. Now let $L$ be a $Lambda$-module, and form the
sequence of additive groups
#idx("deleted projective resolution")
$
  Hom(bold(P), L): 0 -> Hom(P_0, L) stretch(->)^(phi_1^*) Hom(P_1, L)
  stretch(->)^(phi_2^*) Hom(P_2, L) -> dots.c,
$
where (as usual) $Hom$ is an abbreviation for $Hom_Lambda$. By
@eq:composition-induced-maps we have
$
  (phi_(i+1))^* dot (phi_i)^* = (phi_i dot phi_(i+1))^* = 0, quad i >= 1,
$
and therefore $im phi_i^* subset ker phi_(i+1)^*$. Now define
$
  Ext_Lambda^n (N, L) = ker phi_(n+1)^* slash im phi_n^*, quad n >= 1.
$ <eq:ext-n>
This yields a sequence of additive groups $Ext_Lambda^1 (N, L)$,
$Ext_Lambda^2 (N, L), dots.c$, the first of which coincides with that given in
@eq:ext-one.

#source(30)
#remark(kind: "Remarks")[
  + Up to isomorphism, the group $Ext_Lambda^n (N, L)$ depends only upon the
    modules $N$ and $L$, and not upon the choice of the projective resolution
    @eq:projective-resolution. (See references.)
  + We could have defined $Ext_Lambda^0 (N, L)$ to be $ker phi_1^*$. However,
    the exactness of the sequence
    $
      P_1 stretch(->)^(phi_1) P_0 stretch(->)^(phi_0) N -> 0
    $
    implies the exactness of the sequence
    $
      0 -> Hom(N, L) stretch(->)^(phi_0^*) Hom(P_0, L)
      stretch(->)^(phi_1^*) Hom(P_1, L),
    $
    by @th:hom-left-exact[(ii)]. Therefore
    $
      ker phi_1^* tilde.equiv im phi_0^* tilde.equiv Hom(N, L).
    $
    It is therefore customary to identify $Ext^0 (N, L)$ with $Hom(N, L)$.
  + The groups $Ext^n (N, L)$ may also be computed by keeping $N$ fixed, and
    using an injective resolution of $L$ (see references).
  + The groups $Ext^n (N, L)$, $n >= 1$, have many of the same properties as
    $Hom(N, L)$. For instance, $Ext^n$ is additive in each variable:
    $
      Ext^n (N_1 dotplus N_2, L) & tilde.equiv
                                   Ext^n (N_1, L) dotplus Ext^n (N_2, L), \
      Ext^n (N, L_1 dotplus L_2) & tilde.equiv
                                   Ext^n (N, L_1) dotplus Ext^n (N, L_2).
    $
    Further, $Ext^n$ is contravariant in the first variable, and covariant in
    the second variable. Thus, each $f in Hom(N, N')$ induces additive
    homomorphisms
    $
      f_n^*: Ext^n (N', L) -> Ext^n (N, L), quad n >= 1.
    $
    Likewise, each $g in Hom(L, L')$ induces additive homomorphisms
    $
      (g_*)_n: Ext^n (N, L) -> Ext^n (N, L'), quad n >= 1.
    $
  + If $N$ is a projective module, then $0 -> N -> N -> 0$ gives a projective
    resolution of $N$. It follows at once from Definition @eq:ext-n that
    $Ext^n (N, L) = 0$ for all $L$ and all $n >= 1$. Conversely, it may be shown
    that if $Ext^1 (N, L) = 0$ for all $L$, then $N$ is projective.
] <rem:ext-properties>

One of the most important properties of the groups $Ext^n$ is as follows (see
references):

#theorem(title: [Long exact sequence for $Ext$])[
  Let
  $
    0 -> A stretch(->)^f B stretch(->)^g C -> 0
  $
  be a short exact sequence of $Lambda$-modules, and let $L$ be any
  $Lambda$-module. Then there is a long exact sequence of extension groups
  #source(31)
  $
    0 & -> Hom(C, L) stretch(->)^(g^*) Hom(B, L)
        stretch(->)^(f^*) Hom(A, L) \
      & stretch(->)^(partial_0) Ext^1 (C, L) stretch(->)^(g^*) Ext^1 (B, L)
        stretch(->)^(f^*) Ext^1 (A, L) \
      & stretch(->)^(partial_1) Ext^2 (C, L) stretch(->)^(g^*) Ext^2 (B, L)
        stretch(->)^(f^*) Ext^2 (A, L) stretch(->)^(partial_2) dots.c.
  $
] <th:long-exact-ext>

#remark(kind: "Remarks")[
  + We have written $Hom$, $Ext$ instead of $Hom_Lambda$, $Ext_Lambda$, for
    convenience. The subscripts on the various maps $g^*$, $f^*$ have also been
    omitted; in accordance with the notation of @rem:ext-properties[(iv)], we
    should have denoted by $g_n^*$ the map $Ext^n (C, L) -> Ext^n (B, L)$
    induced by $g$.
  + It is instructive to compare @th:long-exact-ext[Theorem] with
    @th:hom-left-exact[(ii)]; we now see that @th:hom-left-exact[(ii)] gives the
    start of the long exact sequence of groups occurring in @th:long-exact-ext.
    Furthermore, we can describe the homomorphism $partial_0$ explicitly,
    provided we view $Ext^1 (C, L)$ as the set of equivalence classes of
    extensions of $C$ by $L$. To be precise, given any $h in Hom(A, L)$, we
    define $partial_0 (h)$ to be the equivalence class of the extension
    occurring in the bottom row of the commutative diagram
    $
      #ladder(
        ($0$, $A$, $B$, $C$, $0$),
        ($0$, $L$, $X$, $C$, $0.$),
        (none, $h$, [], $1_C$, none),
        top-maps: ([], $f$, $g$, []),
        dotted-down: (2, 3),
        dotted-bottom: (1, 2),
      )
    $
    Here, $X$ represents the pushout of the pair of maps $(f, h)$, and the
    dotted arrows denote maps defined as in the discussion preceding
    @eq:ext-one.
  + It is somewhat more difficult to describe the additive homomorphisms
    $partial_1, partial_2, dots$ explicitly. One procedure is to define them
    recursively, using the dimension-shifting techniques given in (iv) below.
    Another method uses the fact @rem:ext-properties[(iii)] that we can compute
    all of the groups $Ext^n (dot, L)$ by starting with an injective resolution
    of $L$; in this context, the long exact sequence of @th:long-exact-ext
    arises naturally from an exact triangle associated with an exact sequence of
    graded complexes.
  + @eq:ext-one[Formula] now appears in a more natural setting. From the short
    exact sequence
    $
      0 -> K stretch(->)^psi P stretch(->)^phi N -> 0, quad
      P "projective",
    $
    we obtain a long exact sequence of additive groups
    $
      Hom(P, L) stretch(->)^(psi^*) Hom(K, L) -> Ext^1 (N, L)
      -> Ext^1 (P, L) -> dots.c.
    $
    But $Ext^1 (P, L) = 0$ by @rem:ext-properties[(v)], and so we obtain an
    isomorphism between the expressions given in @eq:ext-one.

    Furthermore, since $Ext^n (P, L) = 0$, $n >= 1$, we obtain an isomorphism
    $
      Ext^(n+1) (N, L) tilde.equiv Ext^n (K, L), quad n >= 1,
    $
    for each module $L$. By means of this formula, the calculation of
    $Ext^(n+1)$ may #source(32)be reduced to that of $Ext^n$. This procedure is
    called _dimension shifting_. A more general version is as follows: Given a
    $Lambda$-exact sequence
    #idx("dimension shifting")
    $
      0 -> K_n -> P_n -> P_(n-1) -> dots.c -> P_0 -> N -> 0,
    $ <eq:dimension-shifting-sequence>
    where $P_i$ is projective, $0 <= i <= n$, then for each $Lambda$-module $L$
    and for each $m >= 1$, there is an isomorphism of additive groups
    $
      Ext^(m+n+1) (N, L) tilde.equiv Ext^m (K_n, L).
    $ <eq:dimension-shifting>
  + Let $N$ be a $Lambda$-module, and let
    $
      0 -> A stretch(->)^f B stretch(->)^g C -> 0
    $
    be a $Lambda$-exact sequence. An analogue of @th:long-exact-ext[Theorem]
    states that there is a long exact sequence of extension groups
    $
      0 -> Hom(N, A) stretch(->)^(f_*) Hom(N, B) & stretch(->)^(g_*)
      Hom(N, C) stretch(->)^partial Ext^1 (N, A) \
      stretch(->)^(f_*) Ext^1 (N, B) & stretch(->)^(g_*) Ext^1 (N, C)
      stretch(->)^partial Ext^2 (N, A) -> dots.c.
    $
    We shall not attempt to describe the maps $partial$ occurring here.
] <rem:long-exact-ext>

Another basic property of extension groups is as follows (see references):

#theorem(title: [Ladder theorem])[
  Given a commutative diagram of $Lambda$-modules and $Lambda$-homomorphisms
  with exact rows:
  $
    #ladder(
      ($0$, $A$, $B$, $C$, $0$),
      ($0$, $A'$, $B'$, $C'$, $0,$),
      (none, [], [], [], none),
    )
  $
  and given any $Lambda$-module $L$, there is a commutative diagram of additive
  groups and homomorphisms with exact rows:
  $
    #ladder(
      (
        $0$,
        $Hom(C, L)$,
        $Hom(B, L)$,
        $Hom(A, L)$,
        $Ext^1 (C, L)$,
        $Ext^1 (B, L)$,
        $dots.c$,
      ),
      (
        $0$,
        $Hom(C', L)$,
        $Hom(B', L)$,
        $Hom(A', L)$,
        $Ext^1 (C', L)$,
        $Ext^1 (B', L)$,
        $dots.c.$,
      ),
      (none, [], [], [], [], [], none),
      upward: true,
      gap: 2mm,
      inset: 0.8mm,
    )
  $
  #idx("Ladder Theorem", target: [@th:ladder])
] <th:ladder>

We conclude with some results on finite generation of extension groups. Let $R$
be a commutative ring, and let $Lambda$ be an $R$-algebra. Then $Lambda$ itself,
and all $Lambda$-modules, can be viewed as $R$-modules. If $L, M, dots$ denote
$Lambda$-modules, then the additive groups $Hom_Lambda (L, M)$,
$L times.o_Lambda M$, $Ext_Lambda^n (L, M)$ $(n >= 1)$ are also $R$-modules, and
all of the various maps so far mentioned in this section are $R$-homomorphisms.

In particular, suppose that $R$ is a noetherian commutative ring, and that
$Lambda$ is finitely generated as $R$-module. For any $Lambda$-module $N$ which
is finitely generated over $R$, all of the $Lambda$-modules occurring in a
projective resolution of $N$ may be chosen finitely generated over $R$. This
readily implies

#source(33)
#theorem[
  Let $Lambda$ be an $R$-algebra, finitely generated as module over the
  commutative noetherian ring $R$. Let $L, M, dots$ denote $Lambda$-modules
  which are finitely generated over $R$ (or equivalently, over $Lambda$). Then
  the $R$-modules
  $
    Hom_Lambda (L, M), quad L times.o_Lambda M, quad
    Ext_Lambda^n (L, M), quad n >= 1,
  $
  are also finitely generated over $R$.
] <th:finite-generation-hom-ext>

=== Change of rings in Hom and Ext <ss:change-of-rings>

Throughout this section let $R$ be a commutative ring with unity element.
Suppose for the moment that $R'$ is a ring of quotients of $R$ with respect to
some multiplicative subset of $R$ (see §~@ss:rings-of-quotients). For each
$R$-module $M$, we may form the $R'$-module
$
  M' = R' times.o_R M.
$
It is often necessary to know how $Hom$ and $Ext$ behave under passage from $R$
to $R'$. The aim of this section is to establish formulas such as
$
  R' times.o_R Hom_R (M, N) tilde.equiv Hom_(R') (M', N')
$
and likewise for $Ext$, assuming that the $R$-modules $M$ and $N$ satisfy some
mild hypotheses. A significant role is played by the fact that $R'$ is $R$-flat
(see §~@ss:projective-and-flat-modules). We shall prove formulas of the above
type in somewhat more general circumstances, which will in fact be met later on.

Let $Lambda^((r))$ denote the left $Lambda$-module which is the external direct
sum of $r$ copies of $Lambda$. If $M$ is any finitely generated left
$Lambda$-module, there is an epimorphism $phi_0: Lambda^((r)) -> M$ for some
$r$. If $Lambda$ is left noetherian, then by @th:noetherian-equivalences
$ker phi_0$ is also finitely generated, and so there is an epimorphism
$phi_1: Lambda^((s)) -> ker phi_0$ for some $s$. Thus we obtain a $Lambda$-exact
sequence
$
  Lambda^((s)) -> Lambda^((r)) -> M -> 0.
$ <eq:finite-presentation>
Even if $Lambda$ is not necessarily noetherian, it may happen that the module
$M$ occurs in some sequence of this type, with $r$, $s$ finite. In such case, we
say that $M$ is a _finitely presented_ $Lambda$-module. We emphasize that when
$Lambda$ is left noetherian, every finitely generated left $Lambda$-module is
necessarily finitely presented.
#idx("finitely presented")

Now let $Lambda$ and $Gamma$ be $R$-algebras and let $M, N, dots$ be left
$Lambda$-modules. Set
$
  Lambda' = Gamma times.o_R Lambda, quad M' = Gamma times.o_R M, dots,
$
so $M'$ is a left module over the $R$-algebra $Lambda'$. There exists an
$R$-homomorphism
$
  alpha: Gamma times.o_R Hom_Lambda (M, N) -> Hom_(Lambda') (M', N'),
$ <eq:change-of-rings-map>
given by
$
  alpha(gamma times.o f) = gamma_r times.o f, quad gamma in Gamma, quad
  f in Hom_Lambda (M, N),
$
#source(34)where $gamma_r$ denotes the right multiplication by $gamma$ acting on
$Gamma$. By virtue of the bimodule structures $lmodule(Gamma, Gamma)_R$ and
$lmodule(Lambda', (M'))_Gamma$, both sides of @eq:change-of-rings-map have the
structure of left $Gamma$-modules. It is easily checked that $alpha$ is a left
$Gamma$-homomorphism. Analogously, the bimodule structures $Gamma_(Gamma, R)$
and $lmodule(Lambda', (N'))_Gamma$ make the expressions in
@eq:change-of-rings-map into right $Gamma$-modules, and $alpha$ is also a right
$Gamma$-homomorphism.

#theorem[
  Let $Lambda$ and $Gamma$ be $R$-algebras, $M$ and $N$ left $Lambda$-modules.
  Suppose that $Gamma$ is $R$-flat, and that $M$ is finitely generated as
  $Lambda$-module. Then the map $alpha$ in @eq:change-of-rings-map is a
  two-sided $Gamma$-monomorphism.
] <th:change-of-rings-monic>

#proof[
  There is a $Lambda$-exact sequence
  $
    0 -> K -> Lambda^((r)) -> M -> 0
  $
  for some $r$. It follows from @th:hom-left-exact that the sequence of
  $R$-modules
  $
    0 -> Hom_Lambda (M, N) -> Hom_Lambda (Lambda^((r)), N)
  $
  is also exact. Since $Gamma$ is $R$-flat, exactness is preserved when the
  functor $Gamma times.o_R dot$ is applied to the above two sequences. We obtain
  two new exact sequences:
  $
    0 -> K' -> Lambda'^((r)) -> M' -> 0,
  $
  and
  $
    0 -> Gamma times.o_R Hom_Lambda (M, N) ->
    Gamma times.o_R Hom_Lambda (Lambda^((r)), N).
  $
  By virtue of @th:hom-left-exact, the first of these sequences gives rise to an
  exact sequence
  $
    0 -> Hom_(Lambda') (M', N') -> Hom_(Lambda') (Lambda'^((r)), N').
  $
  Therefore we obtain a commutative diagram with exact rows:
  $
    #ladder(
      (
        $0$,
        $Gamma times.o_R Hom_Lambda (M, N)$,
        $Gamma times.o_R Hom_Lambda (Lambda^((r)), N)$,
      ),
      ($0$, $Hom_(Lambda') (M', N')$, $Hom_(Lambda') (Lambda'^((r)), N'),$),
      (none, $alpha$, $alpha_1$),
      down-side: right,
    )
  $
  in which the vertical maps $alpha$, $alpha_1$ are precisely those given by
  @eq:change-of-rings-map. But $alpha_1$ is an isomorphism, since
  @th:hom-isomorphisms gives
  $
    Gamma times.o_R Hom_Lambda (Lambda^((r)), N) tilde.equiv
    Gamma times.o_R N^((r)) tilde.equiv (N')^((r)) tilde.equiv
    Hom_(Lambda') (Lambda'^((r)), N').
  $
  It follows at once that $alpha$ is monic, and the theorem is proved.
]

A variant of the preceding result is as follows:

#theorem(major: true)[
  Let $Lambda$ and $Gamma$ be $R$-algebras, $M$ and $N$ left $Lambda$-modules.
  Suppose that $Gamma$ is $R$-flat, and that $M$ is a finitely presented
  $Lambda$-module. Then the map $alpha$ in @eq:change-of-rings-map is a
  two-sided $Gamma$-isomorphism.
] <th:change-of-rings-iso>

#proof[
  #source(35)There is a $Lambda$-exact sequence
  $
    Lambda^((s)) -> Lambda^((r)) -> M -> 0
  $
  for some $r$ and $s$. By @th:hom-left-exact, the sequence
  $
    0 -> Hom_Lambda (M, N) -> Hom_Lambda (Lambda^((r)), N)
    -> Hom_Lambda (Lambda^((s)), N)
  $
  is $R$-exact. As in the proof of @th:change-of-rings-monic, we obtain a
  commutative diagram with exact rows:
  $
    #ladder(
      (
        $0$,
        $Gamma times.o_R Hom_Lambda (M, N)$,
        $Gamma times.o_R Hom_Lambda (Lambda^((r)), N)$,
        $Gamma times.o_R Hom_Lambda (Lambda^((s)), N)$,
      ),
      (
        $0$,
        $Hom_(Lambda') (M', N')$,
        $Hom_(Lambda') (Lambda'^((r)), N')$,
        $Hom_(Lambda') (Lambda'^((s)), N').$,
      ),
      (none, $alpha$, $alpha_1$, $alpha_2$),
      down-side: right,
    )
  $
  As in @th:change-of-rings-monic, both maps $alpha_1$ and $alpha_2$ are
  isomorphisms. This implies at once that $alpha$ is an isomorphism, and the
  theorem is proved.
]

#theorem(major: true, title: [Change of rings])[
  Let $R$ be a commutative ring, and let $Gamma$ and $Lambda$ be $R$-algebras
  such that $Lambda$ is left noetherian and $Gamma$ is $R$-flat. Let $M$ be a
  finitely generated left $Lambda$-module, and let $N$ be arbitrary. Then the
  two-sided $Gamma$-isomorphism given by @eq:change-of-rings-map is the first of
  a family of two-sided $Gamma$-isomorphisms
  $
    Gamma times.o_R Ext_Lambda^n (M, N) tilde.equiv
    Ext_(Lambda')^n (M', N'), quad n >= 0,
  $
  where
  $
    Lambda' = Gamma times.o_R Lambda, quad M' = Gamma times.o_R M, quad
    N' = Gamma times.o_R N.
  $
  #idx("Change of Rings Theorem", target: [@th:change-of-rings-ext])
] <th:change-of-rings-ext>

#proof[
  The hypotheses on $M$ and $Lambda$ imply that $M$ is finitely presented, so
  the map $alpha$ in @eq:change-of-rings-map is an isomorphism by
  @th:change-of-rings-iso. Now let
  $
    --> P_2 stretch(-->)^(phi_2) P_1 stretch(-->)^(phi_1) P_0 --> M --> 0
  $
  be a free $Lambda$-resolution of $M$, chosen so that each $P_i$ is
  $Lambda$-free on a finite number of generators. (Such a resolution exists
  since $Lambda$ is left noetherian.) Then forming the sequence
  $
    0 --> Hom_Lambda (P_0, N) stretch(-->)^(phi_1^*) Hom_Lambda (P_1, N)
    stretch(-->)^(phi_2^*) dots.c,
  $ <eq:hom-resolution>
  we have (by @eq:ext-n)
  $
    Ext_Lambda^n (M, N) tilde.equiv ker phi_(n+1)^* slash im phi_n^*, quad
    n >= 1.
  $
  Since $Gamma$ is $R$-flat, we have
  $
    Gamma times.o_R Ext_Lambda^n (M, N) tilde.equiv
    ker 1 times.o phi_(n+1)^* slash im 1 times.o phi_n^*,
  $ <eq:flat-ext>
  where for $n >= 1$,
  #source(36)
  $
    1 times.o phi_n^*: Gamma times.o_R Hom_Lambda (P_(n-1), N) ->
    Gamma times.o_R Hom_Lambda (P_n, N).
  $
  By @th:change-of-rings-iso, the vertical arrows in the following commutative
  diagram are two-sided $Gamma$-isomorphisms:
  $
    #square(
      $Gamma times.o_R Hom_Lambda (P_(n-1), N)$,
      $Gamma times.o_R Hom_Lambda (P_n, N)$,
      $Hom_(Lambda') (P'_(n-1), N')$,
      $Hom_(Lambda') (P'_n, N').$,
      $1 times.o phi_n^*$,
      [],
      [],
      $psi_n^*$,
    )
  $ <eq:change-of-rings-square>
  The map $psi_n^*$ occurring above is obtained as follows: applying the exact
  functor $Gamma times.o_R dot$ to the original free resolution of $M$, we
  obtain a free $Lambda'$-resolution of $M'$, namely,
  $
    --> P'_2 stretch(-->)^(psi_2) P'_1 stretch(-->)^(psi_1) P'_0 --> M'
    --> 0.
  $
  This in turn yields a sequence
  $
    0 --> Hom_(Lambda') (P'_0, N') stretch(-->)^(psi_1^*)
    Hom_(Lambda') (P'_1, N') stretch(-->)^(psi_2^*) dots.c,
  $
  in which the maps $psi_n^*$ occur. By definition,
  $
    Ext_(Lambda')^n (M', N') = ker psi_(n+1)^* slash im psi_n^*.
  $
  Comparing this formula with that given in @eq:flat-ext, and using the fact
  that the vertical arrows in the commutative diagram @eq:change-of-rings-square
  are isomorphisms, we conclude at once that
  $
    Gamma times.o_R Ext_Lambda^n (M, N) tilde.equiv
    Ext_(Lambda')^n (M', N'), quad n >= 1.
  $
  This is a two-sided $Gamma$-isomorphism, since all of the maps occurring in
  the proof are two-sided $Gamma$-maps. The result also holds when $n = 0$, if
  we set $Ext^0 = Hom$. This completes the proof.
]

#corollary[
  Let $R$ be a commutative ring, and let $R'$ be the ring of
  quotients#footnote[See §~@ss:rings-of-quotients.] of $R$ with respect to some
  multiplicative subset of $R$. Let $Lambda$ be any left noetherian $R$-algebra.
  Then for each finitely generated left $Lambda$-module $M$, and any
  $Lambda$-module $N$, there is an $R'$-isomorphism
  $
    R' times.o_R Ext_Lambda^n (M, N) tilde.equiv
    Ext_(Lambda')^n (M', N'), quad n >= 0,
  $
  where $Lambda' = R' times.o_R Lambda$, $M' = R' times.o_R M$, and so on. This
  isomorphism extends that given by @eq:change-of-rings-map for the case
  $n = 0$.
] <cor:localization-ext>

=== Hereditary rings <ss:hereditary-rings>

A ring $Lambda$ with unity element is _left hereditary_ if every left ideal of
$Lambda$ is a projective $Lambda$-module. As we shall see eventually, maximal
orders are #source(37)hereditary rings, and some of the important facts about
maximal orders are actually special cases of assertions about hereditary rings.
#idx("hereditary ring")#idx("left hereditary")

#theorem[
  If $Lambda$ is a left hereditary ring, then every submodule of a free left
  $Lambda$-module $M$ is isomorphic to an external direct sum of left ideals of
  $Lambda$, and is therefore projective.
] <th:hereditary-submodules-of-free>

#proof(head: [_Proof._#footnote[We give the proof only for the case where $M$ is
    finitely generated; it is this special case which arises most frequently in
    practice. For the general case, see Cartan–Eilenberg [@bib:Cartan1956].]])[
  Let ${m_1, dots, m_k}$ be a free $Lambda$-basis of $M$, and let $N$ be any
  submodule of $M$. We shall use induction on $k$ to show that $N$ is isomorphic
  to an external direct sum of left ideals of $Lambda$. The result is obvious
  for $k = 1$, so now let $k > 1$, and assume that the theorem holds for
  submodules of $M'$, where $M' = Lambda m_2 + dots.c + Lambda m_k$.

  Each $n in N$ is expressible in the form
  $
    n = r_1 m_1 + dots.c + r_k m_k, quad r_i in Lambda,
  $
  with uniquely determined coefficients ${r_i}$. Let $J$ be the set of all first
  coefficients $r_1$ which occur as $n$ ranges over all elements of $N$. Then
  $J$ is a left ideal of $Lambda$, and there is an epimorphism $phi: N -> J$
  given by $phi(n) = r_1$, $n in N$. Clearly $ker phi = N inter M'$, so there is
  a $Lambda$-exact sequence
  $
    0 --> N inter M' --> N stretch(-->)^phi J --> 0.
  $
  Since $Lambda$ is left hereditary, the left ideal $J$ is $Lambda$-projective,
  and so the above sequence splits by @th:projective-criteria. Therefore
  $
    N tilde.equiv J dotplus N inter M'.
  $
  But $N inter M'$ is a submodule of $M'$, and thus $N inter M'$ is isomorphic
  to an external direct sum of left ideals of $Lambda$, by the induction
  hypothesis. Hence $N$ is also isomorphic to such a sum. Finally, each summand
  is projective, whence so is $N$.
]

#remark(kind: "Remarks")[
  + If the ring $Lambda$ has the property that submodules of free left modules
    are projective, then in particular all left ideals of $Lambda$ are
    projective. By @th:hereditary-submodules-of-free, we may conclude that
    $Lambda$ is left hereditary if and only if submodules of free modules are
    projective.
  + The importance of @th:hereditary-submodules-of-free is that it gives us a
    structure theorem for submodules of free $Lambda$-modules when $Lambda$ is
    hereditary. This structure theorem generalizes the one valid for modules
    over a principal ideal domain, since clearly every such domain is
    hereditary. The above proof shows further that #source(38)a submodule of a
    free module on $k$ generators is isomorphic to an external direct sum of at
    most $k$ left ideals of $Lambda$.
  + There are examples of rings which are left hereditary but not right
    hereditary. However, if $Lambda$ is left and right noetherian, then $Lambda$
    is left hereditary if and only if $Lambda$ is right hereditary (see Rotman
    [@bib:Rotman1970, Corollary~9.20]; the result is due to M. Auslander).
  + The proof of @th:hereditary-submodules-of-free, for the case where $M$ is
    not finitely generated, proceeds in much the same manner as the above proof.
    The main difference is that $k$ must be allowed to be transfinite, and the
    proof uses transfinite induction.
] <rem:hereditary>

#heading(level: 3, numbering: none, outlined: false)[Exercises]

#exercise[
  Let
  $
    #square($Y$, $M_1$, $M_2$, $overline(M)$, $g_1$, $g_2$, $f_1$, $f_2$)
  $
  be a pullback diagram of $Lambda$-modules. Prove
  + $g_2$ induces an isomorphism $ker g_1 tilde.equiv ker f_2$.
  + If $f_2$ is epic, then so is $g_1$.
] <exc:pullback-kernels>

#exercise[
  Let
  $
    #square($L$, $N_1$, $N_2$, $X$, $f_1$, $f_2$, $g_1$, $g_2$)
  $
  be a pushout diagram of $Lambda$-modules. Prove
  + $g_1$ induces an isomorphism $cok f_1 tilde.equiv cok g_2$.
  + If $f_1$ is monic, then so is $g_2$.
] <exc:pushout-exact-rows>

#exercise[
  Let $Gamma$ and $Delta$ be rings, and suppose we have modules $M_Gamma$,
  $L_Delta$, and a bimodule $lmodule(Delta, N)_Gamma$. Show that there is a
  well-defined additive homomorphism
  $
    alpha: L times.o_Delta Hom_Gamma (M, N) ->
    Hom_Gamma (M, L times.o_Delta N),
  $
  defined by $l times.o f -> (l, f)$, where
  $
    (l, f) m = l times.o f m, quad l in L, quad f in Hom_Gamma (M, N), quad
    m in M.
  $
  Prove that $alpha$ is an isomorphism whenever $L$ is $Delta$-flat and $M$ is a
  finitely presented $Gamma$-module. #hint[@exc:tensor-hom-flat][Imitate the
    proof of @th:change-of-rings-iso, using $times.o_Delta$ in place of
    $times.o_R$.] <hint:tensor-hom-flat>
] <exc:tensor-hom-flat>

#exercise[
  Let $Delta$ be a ring, and let $L_Delta$ be flat, and $M_Delta$ finitely
  presented. Use Exercise~@exc:tensor-hom-flat to prove that
  $
    L times.o_Delta Hom_Delta (M, Delta) tilde.equiv Hom_Delta (M, L).
  $
] <exc:tensor-dual-flat>

#exercise[
  #source(39)Let $Delta$ be a ring, $L_Delta$ any module, and let $M_Delta$ be a
  finitely generated projective module. Prove that
  $
    L times.o_Delta Hom_Delta (M, Delta) tilde.equiv Hom_Delta (M, L).
  $
  #hint[@exc:tensor-dual-projective][Use @rem:free-then-projective.]
  <hint:tensor-dual-projective>
] <exc:tensor-dual-projective>

#exercise[
  Let $phi: R -> S$ be a homomorphism of commutative rings, and let $J$ be an
  ideal in $R$. Prove that
  $
    S times.o_R (R slash J) tilde.equiv S slash S dot phi(J)
  $
  as $S$-modules.
] <exc:base-change-quotient>

#exercise[
  Prove _Schanuel's Lemma_: Given two exact sequences of left $Lambda$-modules
  $
    0 -> M -> P stretch(->)^phi X -> 0, quad
    0 -> M' -> P' stretch(->)^psi X -> 0,
  $
  in which $P$ and $P'$ are projective, there is a $Lambda$-isomorphism
  $
    M' dotplus P tilde.equiv M dotplus P'.
  $
  #idx("Schanuel's Lemma")
  #hint[@exc:schanuel][Let $A$ be the pullback of the pair of maps $phi$, $psi$.
    Then there exist $Lambda$-exact sequences
    $
      0 -> K -> A -> P -> 0, quad 0 -> K' -> A -> P' -> 0,
    $
    with $K tilde.equiv ker psi tilde.equiv M'$,
    $K' tilde.equiv ker phi tilde.equiv M$. Since $P$ and $P'$ are projective,
    $A tilde.equiv P dotplus K tilde.equiv P' dotplus K'$.] <hint:schanuel>
] <exc:schanuel>

#exercise[
  Prove the _Snake Lemma_: Given a commutative diagram of modules, with exact
  rows:
  $
    #ladder(
      (none, $A$, $B$, $C$, $0$),
      ($0$, $A'$, $B'$, $C',$, none),
      (none, $alpha$, $beta$, $gamma$, none),
      top-maps: (none, $phi$, [], []),
      bottom-maps: ([], [], $psi$, none),
    )
  $
  there is an exact sequence
  $
    ker alpha stretch(-->)^(phi_*) ker beta --> ker gamma
    stretch(-->)^delta cok alpha --> cok beta stretch(-->)^(psi_*) cok gamma.
  $
  If $phi$ is monic, so is $phi_*$. If $psi$ is epic, so is $psi_*$. The lemma
  remains true for a diagram of groups and group homomorphisms, if each of the
  groups $A'$, $B'$ and $C'$ is commutative.
  #idx("Snake Lemma")
  #hint[@exc:snake][Define $delta$ by $delta(c) = a' + im alpha$, where
    $
      a' -> b', quad b' = beta(b), quad b -> c.
    $] <hint:snake>
] <exc:snake>
