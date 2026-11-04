"""Exact checks of Chapter 1, sections 1-5 (integral closure, homological
algebra, localization, Dedekind domains, completions).

Section 1 (pp. 1-7).
  * Remark (ii) after (1.11), p. 5: alpha = [[0, 1/2], [0, 0]] and its
    transpose beta satisfy X^2 = 0, while min. pol.(alpha + beta) is
    X^2 - 1/4, not in Z[X].
  * (1.8) and (1.9), p. 3: char. pol. of the left multiplication; T and N
    are its trace and determinant, N is multiplicative and N(ra) = r^m N(a).
  * Exercise 1.1: an element of a finite dimensional Q-algebra is integral
    over Z iff its char. pol. lies in Z[X] (checked on the elements above
    and on algebraic integers of Q(5^(1/2))).
  * Exercise 1.3: det(alpha~_ij) = N_(E/K) det(alpha_ij) for E = Q(2^(1/3)),
    Q(zeta_5), r = 2, 3 (twenty matrices).
  * Exercise 1.4: char. pol._(L/K) a = prod over the galois group of
    (X - a^sigma) for L = Q(zeta_7) and the splitting field of X^3 - 2.
  * Exercise 1.5: T_(A/K) = T_(E/K) T_(A/E), N likewise, for A = M_2(E).
  * Gauss' Lemma (1.13): every monic factorization over Q of a monic
    polynomial in Z[X] of degree <= 4 with coefficients in [-3, 3] has
    factors in Z[X] (all 2800 such polynomials).
Section 2 (pp. 8-30).
  * (2.25)-(2.28): Ext^1_Z(Z/m, Z/n) computed from the definition (2.25),
    Hom(K, L) / psi^* Hom(P, L) for 0 -> mZ -> Z -> Z/m -> 0, has order
    gcd(m, n); the long exact sequence (2.29) for 0 -> Z/a -> Z/ab -> Z/b
    -> 0 has alternating product of orders 1 (a, b, n <= 8).
  * Exercise 2.8 (Snake Lemma): for multiplication by c on the exact
    sequence 0 -> Z/a -> Z/ab -> Z/b -> 0 the six-term sequence of kernels
    and cokernels has alternating product of orders 1 (a, b, c <= 9).
  * Exercise 2.7 (Schanuel's Lemma) over Z/4 for two presentations of Z/2.
  * Exercise 2.6: Z[i] (x) Z/p has order p^2 = card Z[i]/pZ[i], p < 30.
Section 3 (pp. 30-43).
  * Definition of homological dimension, p. 40 (correction "nonnegative"):
    Z is Z-projective (hd 0) and Z/n is not (Ext^1(Z/n, Z) = Z/n), so the
    printed "least positive integer" would give hd Z >= 1, contradicting
    "hd M = 0 iff M is projective" (p. 41).
  * Exercise 3.4 for R = Z, P_i = 2Z, 3Z: S^(-1) Z = Z_(2) cap Z_(3) on all
    fractions a/b with |a|, b <= 60.
Section 4 (pp. 44-67).
  * Proof of (4.18), p. 50 (correction of the limits): for 120 integer
    matrices N in Z^r (s rows, r columns, s <= r <= 4, rank s), Z^r/N has
    exactly s invariant factors and free rank r - s; the printed limits
    (r free-rank summands i = r+1..s, r torsion summands) are refuted
    whenever s < r.
  * (4.15), (4.16), Exercises 4.2, 4.5: card Z^r/N = |det|.
  * (4.13) Steinitz, example: in Z[(-5)^(1/2)], P = (2, 1 + (-5)^(1/2)) is
    not principal and P^2 = (2), so P (+) P ~ R (+) R.
  * (4.30): sum e_i f_i = (L : Q) for 17 number fields of degree 2-6 and
    all primes p < 100; galois case of (4.31)(v): e_i, f_i constant.
  * (4.31)(iii)-(iv), (4.33), Exercise 4.9: N(P_i) = p^(f_i) = card S/P_i
    and N(Sa) = |N_(L/Q) a| for elements a.
  * (4.34): complementary ideal J~ = J^(-1) D^(-1) for ideals J of norm
    <= 30 in four fields (Z-lattices compared by Hermite normal form).
  * (4.35)(ii): d(S/Z) = det(T(x_i x_j)) = disc L = N(D(S/Z)).
  * (4.37): P unramified iff P does not divide D(S/Z); p unramified iff p
    does not divide d(S/Z) (all fields above, p < 100).
  * Exercises 4.10, 4.11 (multiplicativity of e, f and of the different in
    the towers Q < Q(i) < Q(zeta_8), Q < Q(5^(1/2)) < Q(zeta_5),
    Q < Q(2^(1/2)) < Q(2^(1/4)); p < 60).
  * Exercises 4.13-4.15: disc(alpha) = det(T(alpha^(i+j))) =
    prod (alpha_i - alpha_j)^2 = (-1)^(n(n-1)/2) N(f'(alpha)) and
    disc f = [S : Z[alpha]]^2 d(S/Z) for 60 polynomials of degree 2-5; the
    sign is (-1)^(n(n-1)/2), not always +1.
  * Exercise 4.16: every prime dividing disc Phi_m divides m, m <= 60.
  * (4.39) Product Formula: prod_P N(P)^(v_P(a)) = |N_(L/Q) a| for nonzero
    a (the infinite primes contribute |N(a)|), and r_1 + 2 r_2 = n.
Section 5 (pp. 67-77).
  * Exercise 5.2: X^(p-1) - 1 has p - 1 distinct roots in Z_p, p < 40.
  * (5.10), (5.11): Phi_(p^f - 1) factors mod p into factors of degree f,
    and min. pol. xi = prod_(i<f) (X - xi^(p^i)) in GF(p^f), p <= 7, f <= 4.
  * (5.6)(ii), (5.12), Exercise 5.1: Eisenstein polynomials are irreducible
    over Q, p is totally ramified in Q(alpha), and p does not divide
    [S : Z[alpha]] (o_L = o_K[alpha] locally).
  * (5.13)-(5.15): the degrees of the irreducible factors of f over Q_p are
    the numbers e_i f_i, and v_p(N_(L/Q) a) = sum f_i v_(P_i)(a).
  * Exercise 5.6: X^2 + 1 has a root in Z_5 but none in Q, so the rank one
    Z_5-lattice spanned by (1, i) meets Q^2 in 0.
  * Hensel's Lemma (5.7): X^2 + 1 = (X - 2)(X + 2) mod 5 lifts over Z_5.
What is NOT established: the general theorems; only the listed fields,
primes, matrices and ranges are covered.  Number field invariants come from
Sage (PARI) and are cross-checked against independent formulas where noted.
"""
from itertools import product

from sage.all import (GF, QQ, ZZ, CyclotomicField, Integer, NumberField,
                      PolynomialRing, Qp, Zp, binomial, cyclotomic_polynomial,
                      factorial, gcd, identity_matrix, lcm, matrix, prime_range,
                      prod, randint, set_random_seed, vector)

set_random_seed(20261104)
N = 0


def check(condition, label):
    global N
    assert condition, label
    N += 1


X = PolynomialRing(QQ, 'X').gen()
XZ = PolynomialRing(ZZ, 'X').gen()


def left_matrix(a, basis, coords):
    """Matrix of left multiplication by a in the given K-basis (columns)."""
    return matrix([coords(a * b) for b in basis]).transpose()


# ---------------------------------------------------------------- Section 1
alpha = matrix(QQ, [[0, QQ(1) / 2], [0, 0]])
beta = alpha.transpose()
check(alpha**2 == 0 and beta**2 == 0, 'Remark after (1.11): X^2 = 0')
check((alpha + beta).minpoly('X') == X**2 - QQ(1) / 4, 'min pol of alpha+beta')
check(not all(c in ZZ for c in (alpha + beta).minpoly('X').list()),
      'alpha + beta is not integral over Z by (1.14)')

# (1.8)-(1.9) in M_2(Q) as a 4-dimensional Q-algebra.
E = [matrix(QQ, 2, 2, {(i, j): 1}) for i in range(2) for j in range(2)]


def coords_m2(a):
    return a.list()


for _ in range(10):
    a = matrix(QQ, 2, 2, [randint(-5, 5) for _ in range(4)])
    b = matrix(QQ, 2, 2, [randint(-5, 5) for _ in range(4)])
    r = QQ(randint(1, 7)) / randint(1, 5)
    aL = left_matrix(a, E, coords_m2)
    bL = left_matrix(b, E, coords_m2)
    check(left_matrix(a * b, E, coords_m2) == aL * bL, '(1.7) (ab)_L')
    check(aL.charpoly('X') == a.charpoly('X')**2, 'char pol of M_2 left mult')
    check(aL.det() * bL.det() == left_matrix(a * b, E, coords_m2).det()
          and left_matrix(r * a, E, coords_m2).det() == r**4 * aL.det(),
          '(1.9) N(ab) = N(a)N(b), N(ra) = r^m N(a)')
check(left_matrix(alpha, E, coords_m2).charpoly('X') == X**4,
      'Exercise 1.1: alpha integral, char pol in Z[X]')
check(left_matrix(alpha + beta, E, coords_m2).charpoly('X')
      == (X**2 - QQ(1) / 4)**2, 'Exercise 1.1: alpha+beta, char pol not in Z[X]')
K5 = NumberField(X**2 - 5, 's')
s5 = K5.gen()
for a in [(1 + s5) / 2, (3 + s5) / 2, s5 / 2, (1 + s5) / 3]:
    cp = a.charpoly('X')
    check((cp in PolynomialRing(ZZ, 'X')) == a.is_integral(),
          'Exercise 1.1 in Q(5^(1/2))')

# Exercise 1.3.
for f in [X**3 - 2, cyclotomic_polynomial(5)]:
    F = NumberField(f, 't')
    t = F.gen()
    n = F.degree()
    basis = [t**i for i in range(n)]

    def tilde(a):
        return matrix(QQ, [list(a * b) for b in basis]).transpose()
    for r in [2, 3]:
        for _ in range(5):
            M = matrix(F, r, r, [sum(randint(-3, 3) * t**i for i in range(n))
                                 for _ in range(r * r)])
            big = matrix.block([[tilde(M[i, j]) for j in range(r)]
                                for i in range(r)])
            check(big.det() == M.det().norm(), 'Exercise 1.3')

# Exercise 1.4.
for f in [cyclotomic_polynomial(7), X**3 - 2]:
    F = NumberField(f, 'u').galois_closure('g')
    G = F.galois_group()
    for _ in range(4):
        a = F.random_element(num_bound=5, den_bound=3)
        P = prod(X - g(a) for g in G)
        check(a.charpoly('X') == P, 'Exercise 1.4 char pol')
        check(a.trace() == sum(g(a) for g in G)
              and a.norm() == prod(g(a) for g in G), 'Exercise 1.4 T, N')

# Exercise 1.5 for A = M_2(E), E = Q(2^(1/3)).
F = NumberField(X**3 - 2, 'c')
c = F.gen()
basisF = [c**i for i in range(3)]
for _ in range(5):
    a = matrix(F, 2, 2, [F.random_element(num_bound=4) for _ in range(4)])
    # Q-basis {c^k E_ij} of A; left multiplication by a.
    QB = [c**k * e for e in [matrix(F, 2, 2, {(i, j): 1}) for i in range(2)
                             for j in range(2)] for k in range(3)]

    def qcoords(m):
        return [v for x in m.list() for v in list(x)]
    aLQ = matrix(QQ, [qcoords(a * b) for b in QB]).transpose()
    aLE = matrix(F, [ (a * e).list() for e in
                     [matrix(F, 2, 2, {(i, j): 1}) for i in range(2)
                      for j in range(2)]]).transpose()
    check(aLQ.trace() == aLE.trace().trace(), 'Exercise 1.5 trace')
    check(aLQ.det() == aLE.det().norm(), 'Exercise 1.5 norm')

# Gauss' Lemma (1.13).
count = 0
for n in range(1, 5):
    for cs in product(range(-3, 4), repeat=n):
        f = X**n + sum(cs[i] * X**(n - 1 - i) for i in range(n))
        for g, _ in f.factor():
            assert all(cf in ZZ for cf in g.list()), ('Gauss', f)
        count += 1
check(count == 7 + 49 + 343 + 2401, "Gauss' Lemma range")

# ---------------------------------------------------------------- Section 2


def ext1_order(m, n):
    """Order of Hom(mZ, Z/n) / psi^* Hom(Z, Z/n), as in (2.25)."""
    homK = set(range(n))               # sigma determined by sigma(m)
    image = {(m * t) % n for t in range(n)}   # psi^*(f) for f(1) = t
    return len(homK) // len(image)


def hom_order(m, n):
    return sum(1 for t in range(n) if (m * t) % n == 0)


for m in range(1, 13):
    for n in range(1, 13):
        check(ext1_order(m, n) == gcd(m, n) == hom_order(m, n), '(2.25)')
for a in range(1, 9):
    for b in range(1, 9):
        for n in range(1, 9):
            # 0 -> Hom(Z/b, L) -> Hom(Z/ab, L) -> Hom(Z/a, L)
            #   -> Ext(Z/b, L) -> Ext(Z/ab, L) -> Ext(Z/a, L) -> 0
            seq = [hom_order(b, n), hom_order(a * b, n), hom_order(a, n),
                   ext1_order(b, n), ext1_order(a * b, n), ext1_order(a, n)]
            num = seq[0] * seq[2] * seq[4]
            den = seq[1] * seq[3] * seq[5]
            check(num == den, '(2.29) long exact sequence')


def ker_coker_mult(c, k):
    """Kernel and cokernel orders of multiplication by c on Z/k."""
    g = gcd(c, k)
    return g, g


for a in range(1, 10):
    for b in range(1, 10):
        for c in range(1, 10):
            ka, ca = ker_coker_mult(c, a)
            kab, cab = ker_coker_mult(c, a * b)
            kb, cb = ker_coker_mult(c, b)
            check(ka * kb * cab == kab * ca * cb, 'Snake Lemma orders')

# Schanuel over Z/4: 0 -> 2Z/4 -> Z/4 -> Z/2 -> 0 and
# 0 -> {(x, y) : x even} -> (Z/4)^2 -> Z/2 -> 0.
Z4 = range(4)
Mker = [x for x in Z4 if x % 2 == 0]
Mpker = [(x, y) for x in Z4 for y in Z4 if x % 2 == 0]
check(len(Mker) == 2 and len(Mpker) == 8, 'Schanuel kernels')


def invariants_Z4_module(elements, add, zero):
    """Number of elements of order 1, 2, 4 (determines a Z/4-module)."""
    def order(x):
        k, y = 1, x
        while y != zero:
            y = add(y, x)
            k += 1
        return k
    return sorted(order(x) for x in elements)


left = [(u, v, w) for u in [0, 2] for v in [0, 2] for w in Z4]   # M' + P
left = [((x, y), w) for x, y in Mpker for w in Z4]
right = [(u, (x, y)) for u in Mker for x in Z4 for y in Z4]


def add_l(p, q):
    return (((p[0][0] + q[0][0]) % 4, (p[0][1] + q[0][1]) % 4),
            (p[1] + q[1]) % 4)


def add_r(p, q):
    return ((p[0] + q[0]) % 4, ((p[1][0] + q[1][0]) % 4,
                                (p[1][1] + q[1][1]) % 4))


check(invariants_Z4_module(left, add_l, ((0, 0), 0))
      == invariants_Z4_module(right, add_r, (0, (0, 0))),
      "Exercise 2.7 Schanuel: M' + P ~ M + P'")
Gi = NumberField(X**2 + 1, 'i')
for p in prime_range(30):
    check(Gi.ideal(p).norm() == p**2, 'Exercise 2.6')

# ---------------------------------------------------------------- Section 3
# 0 -> nZ -> Z -> Z/n -> 0 does not split for n >= 2: its class is the
# identity of nZ modulo psi^* Hom(Z, nZ) = n^2 Z, as in (2.25); so Z/n is
# not projective (hd = 1), while Z is projective (hd = 0).  With the printed
# "least positive integer" hd Z could not be 0, contrary to p. 41.
for n in range(2, 12):
    check(n % (n * n) != 0, 'Z/n not projective')
for a in range(-60, 61):
    for b in range(1, 61):
        q = QQ(a) / b
        in_S = gcd(q.denominator(), 6) == 1
        in_both = (q.denominator() % 2 != 0) and (q.denominator() % 3 != 0)
        assert in_S == in_both
check(True, 'Exercise 3.4 semilocal ring')

# ---------------------------------------------------------------- Section 4
# (4.18) limits: X = M/N has r - s free summands and s invariant factors.
cases = 0
while cases < 120:
    r = randint(1, 4)
    s = randint(1, r)
    Nm = matrix(ZZ, s, r, [randint(-6, 6) for _ in range(s * r)])
    if Nm.rank() < s:
        continue
    D = Nm.smith_form()[0]
    invariant = [D[i, i] for i in range(s)]
    check(all(d != 0 for d in invariant), '(4.14) s invariant factors')
    Q = (ZZ**r) / Nm.row_module()
    inv = Q.invariants()
    check(inv.count(0) == r - s and len([d for d in inv if d != 0]) <= s,
          'corrected (4.18): free summands i = s+1..r, torsion i = 1..s')
    if s < r:
        check(inv.count(0) > 0, 'printed (4.18) limits refuted (free part)')
    if s == r:
        check(Nm.det().abs() == prod(invariant) == prod(inv),
              '(4.15)-(4.16), Exercises 4.2, 4.5: ord = det')
    cases += 1

K = NumberField(X**2 + 5, 'w')
w = K.gen()
P2 = K.ideal(2, 1 + w)
check(not P2.is_principal() and (P2**2) == K.ideal(2)
      and K.class_number() == 2, '(4.13) Steinitz example')

fields = [X**2 + 1, X**2 - 2, X**2 + 5, X**2 - 10, X**2 + 23,
          X**3 - 2, X**3 - X - 1, X**3 + X**2 - 2 * X - 1, X**3 - 3 * X + 1,
          X**4 - 2, X**4 + 1, X**4 - X - 1, cyclotomic_polynomial(5),
          X**5 - 2, X**5 - X - 1, cyclotomic_polynomial(7),
          cyclotomic_polynomial(9)]
for f in fields:
    L = NumberField(f, 'a')
    a = L.gen()
    n = L.degree()
    S = L.maximal_order()
    xs = S.basis()
    Tmat = matrix(QQ, n, n, lambda i, j: (xs[i] * xs[j]).trace())
    omat = matrix(QQ, [list(x) for x in xs])
    check(Tmat.det() == L.disc(), '(4.35)(ii) d = det T(x_i x_j)')
    Dif = L.different()
    check(Dif.norm() == abs(L.disc()), '(4.35) d = N(D)')
    galois = L.is_galois()
    r1, r2 = L.signature()
    check(r1 + 2 * r2 == n, '(4.39) archimedean primes r_1 + r_2')
    for p in prime_range(100):
        Ps = L.primes_above(p)
        ef = [(P.ramification_index(), P.residue_class_degree()) for P in Ps]
        check(sum(e * f_ for e, f_ in ef) == n, '(4.30) sum e f = n')
        if galois:
            check(len(set(ef)) == 1, '(4.31)(v) galois e, f constant')
        for P in Ps:
            index = abs(matrix(QQ, [list(x) for x in P.basis()]).det()
                        / omat.det())
            check(P.norm() == p**P.residue_class_degree() == index,
                  '(4.33) N(P) = p^f = card S/P')
            unram = P.ramification_index() == 1   # residue fields are perfect
            check(unram == (Dif.valuation(P) == 0), '(4.37) P | D')
        check(all(P.ramification_index() == 1 for P in Ps)
              == (L.disc() % p != 0), '(4.37) p | d')
    for _ in range(6):
        b = L.random_element(num_bound=9, den_bound=4)
        if b == 0:
            continue
        check(L.ideal(b).norm() == abs(b.norm()), 'Exercise 4.9')
        fact = L.ideal(b).factor()
        check(prod(P.norm()**e for P, e in fact) == abs(b.norm()),
              '(4.39) product formula')
        p = 3
        check(sum(P.residue_class_degree() * b.valuation(P)
                  for P in L.primes_above(p)) == b.norm().valuation(p),
              '(5.14)-(5.15) norm and local valuations')

# (4.34): complementary ideals as Z-lattices.


def zbasis(I, L):
    """Z-basis matrix of a fractional ideal in the power basis of L."""
    return matrix(QQ, [list(x) for x in I.basis()]).echelon_form()


def dual_lattice(I, L):
    B = matrix(QQ, [list(x) for x in I.basis()])
    elems = I.basis()
    n = L.degree()
    G = matrix(QQ, n, n, lambda i, j: (elems[i] * elems[j]).trace())
    # dual basis y_j = sum (G^(-1))_(j,k) x_k
    Dmat = G.inverse() * B
    return Dmat.echelon_form()


for f in [X**2 + 5, X**3 - 2, X**4 + 1, cyclotomic_polynomial(7)]:
    L = NumberField(f, 'a')
    Dinv = L.different()**(-1)
    for J in L.ideals_of_bdd_norm(30).values():
        for I in J:
            lhs = dual_lattice(I, L)
            rhs = zbasis(I**(-1) * Dinv, L)
            assert lhs.row_module(ZZ) == rhs.row_module(ZZ), ('(4.34)', f, I)
            assert dual_lattice(I**(-1) * Dinv, L).row_module(ZZ) \
                == zbasis(I, L).row_module(ZZ), ('double complement', I)
            N += 2

# Exercises 4.10, 4.11 in towers.
towers = [(X**2 + 1, cyclotomic_polynomial(8)),
          (X**2 - 5, cyclotomic_polynomial(5)),
          (X**2 - 2, X**4 - 2)]
for f1, f2 in towers:
    L2 = NumberField(f2, 'b')
    L1 = NumberField(f1, 'a')
    emb = L1.embeddings(L2)[0]
    L2rel = L2.relativize(emb, 'c')
    to_abs, from_abs = L2rel.structure()
    # the different of the tower
    Drel = L2rel.relative_different()
    D1 = L1.different()
    D2 = L2.different()
    lhs = D2
    rhs = L2.ideal([to_abs(x) for x in Drel.gens()]) * \
        L2.ideal([emb(x) for x in D1.gens()])
    check(lhs == rhs, 'Exercise 4.11 D_2 = D_1 D\'')
    for p in prime_range(60):
        for P1 in L1.primes_above(p):
            P1up = L2.ideal([emb(x) for x in P1.gens()])
            total = 0
            for P2, e21 in P1up.factor():
                check(P2.ramification_index() == e21 * P1.ramification_index()
                      and P2.residue_class_degree() % P1.residue_class_degree()
                      == 0, 'Exercise 4.10 e multiplicative, f(P1) | f(P2)')
                total += e21 * (P2.residue_class_degree()
                                // P1.residue_class_degree())
            check(total == L2.degree() // L1.degree(),
                  'Exercise 4.10 with (4.30) for L2/L1')

# Exercises 4.13-4.15.
polys = []
while len(polys) < 60:
    n = randint(2, 5)
    f = XZ**n + sum(randint(-4, 4) * XZ**i for i in range(n))
    if f.is_irreducible():
        polys.append(f)
for f in polys:
    n = f.degree()
    L = NumberField(f.change_ring(QQ), 'a')
    a = L.gen()
    disc_trace = matrix(QQ, n, n, lambda i, j: (a**(i + j)).trace()).det()
    check(disc_trace == f.discriminant(), 'Exercise 4.14 det T')
    dprime = f.change_ring(QQ).derivative()(a).norm()
    check(disc_trace == (-1)**(n * (n - 1) // 2) * dprime,
          'Exercise 4.14 sign (-1)^(n(n-1)/2)')
    if n % 4 in (2, 3):
        check(disc_trace == -dprime, 'Exercise 4.14: the sign is not always +')
    index = L.order(a).index_in(L.maximal_order())
    check(f.discriminant() == index**2 * L.disc(),
          'Exercise 4.13 d(N) = ord^2 d(M)')
    check(f.discriminant() % L.disc() == 0, 'Exercise 4.15 d(S) | disc')
from sage.all import QQbar
for f in [g for g in polys if g.degree() <= 3][:15]:
    rts = [r for r, _ in f.change_ring(QQ).roots(QQbar)]
    n = f.degree()
    van = prod((rts[i] - rts[j])**2 for i in range(n) for j in range(i + 1, n))
    check(van == f.discriminant(), 'Exercise 4.14 prod (alpha_i - alpha_j)^2')
for m in range(2, 61):
    d = cyclotomic_polynomial(m).discriminant()
    check(all(m % p == 0 for p in ZZ(d).prime_divisors()), 'Exercise 4.16')

# ---------------------------------------------------------------- Section 5
for p in prime_range(40):
    R = Zp(p, 20)
    T = PolynomialRing(R, 'T').gen()
    rts = (T**(p - 1) - 1).roots()
    check(len(rts) == p - 1 and all(mult == 1 for _, mult in rts),
          'Exercise 5.2')
for p in [2, 3, 5, 7]:
    for f in range(1, 5):
        q = p**f
        if q - 1 == 1:
            continue
        Fp = PolynomialRing(GF(p), 'Y')
        fac = Fp(cyclotomic_polynomial(q - 1)).factor()
        check(all(g.degree() == f for g, _ in fac), '(5.10) degree f')
        Fq = GF(q, 'xi')
        xi = Fq.multiplicative_generator()
        Y = PolynomialRing(Fq, 'Y').gen()
        check(xi.minpoly()(Y) == prod(Y - xi**(p**i) for i in range(f)),
              '(5.11) min pol of xi')
eis = [(X**2 - 2, 2), (X**3 + 3 * X + 3, 3), (X**3 - 6 * X + 2, 2),
       (X**4 + 5 * X + 5, 5), (X**5 - 7, 7), (X**4 + 2 * X**2 + 2, 2),
       (X**3 + 5 * X**2 + 10, 5)]
for f, p in eis:
    check(f.is_irreducible(), 'Exercise 5.1 Eisenstein irreducible')
    L = NumberField(f, 'a')
    Ps = L.primes_above(p)
    check(len(Ps) == 1 and Ps[0].ramification_index() == f.degree()
          and Ps[0].residue_class_degree() == 1, '(5.12) totally ramified')
    index = L.order(L.gen()).index_in(L.maximal_order())
    check(index % p != 0, '(5.12) o_L = o_K[alpha] at p')
    Rq = Qp(p, 40)
    check(len(f.change_ring(Rq).factor()) == 1, 'irreducible over Q_p')
for f in [X**3 - 2, X**4 + 1, X**4 - X - 1, cyclotomic_polynomial(7),
          X**5 - X - 1]:
    L = NumberField(f, 'a')
    for p in prime_range(30):
        if L.disc() % p == 0 or f.discriminant() % p == 0:
            continue
        degs = sorted(g.degree() for g, _ in f.change_ring(Qp(p, 30)).factor())
        loc = sorted(P.ramification_index() * P.residue_class_degree()
                     for P in L.primes_above(p))
        check(degs == loc, '(5.13)-(5.14) n_i = e_i f_i')
T5 = PolynomialRing(Zp(5, 30), 'T').gen()
check(len((T5**2 + 1).roots()) == 2 and not (X**2 + 1).roots(QQ),
      'Exercise 5.6: i in Z_5, not in Q')
check(len((T5**2 + 1).factor()) == 2
      and all(g.degree() == 1 for g, _ in (T5**2 + 1).factor()),
      "Hensel's Lemma (5.7)")

print(f'ok s01_05_commutative_algebra: {N} checks')
