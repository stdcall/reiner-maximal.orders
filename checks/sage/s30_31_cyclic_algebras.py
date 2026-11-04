"""Exact checks of Sections 30-31: cyclic algebras, local Hasse invariants.

Run with `sage -python`. Crossed products are built from (29.1) as in
s28_29_crossed_products.py. Hilbert symbols, `is_norm`, `is_matrix_ring`,
`ramified_places` and `DiagonalQuadraticForm.is_anisotropic` of Sage are
used as independent references for local splitting.

Section 30 (pp. 259-263).
* (30.1), eq:cyclic-factor-set: the cyclic factor set satisfies (29.2)
  (exponent identity, n <= 30) and u^n = a, over L3 (cubic, conductor 7),
  Q(zeta_5) (order 4), Q(zeta_7) (order 6).
* (30.2): for random normalized factor sets g, a = prod g(s^j, s) lies in
  K^*, v_s^n = a, and a equals N(c_s) times the original a.
* (30.3)(i), (iii), (iv): w = u^s, (c u)^n = N(c) a, f_a f_b = f_(ab).
* (30.4): (L3/Q, s, 2) has exponent 3 (2 is inert, v_2 N(x) = 3 v_P(x)),
  so it is a skewfield.
* (30.6), (30.7): the restriction and inflation identities b = a and
  b = a^((E : L)) for the cyclic factor set, n <= 30 and n, s <= 12.
* Exercise 30.1: for 8 quadratic fields and |a| <= 30, (L/Q, s, a) is
  split iff a is a norm. Exercise 30.4 for all odd p < 2000 (explicit
  alpha with N(alpha) = p and zero divisors when (2/p) = 1; for (2/p) = -1
  no solution mod p (p < 200), p not a norm, p^2 a norm, a skewfield).

Section 31 (pp. 263-271).
* (14.1) as used in (31.1): norms of finite fields are onto (q^m <= 625).
* eq:hasse-invariant and the Caution: for (a, b) = (Q_p(sqrt a)/Q_p, s, b)
  with Q_p(sqrt a)/Q_p unramified (a squarefree, |a|, |b| <= 30, p < 32),
  inv = v_p(b)/2 for the Frobenius s and 0 in the split case, agreeing with
  the Hilbert symbol in all cases.
* (31.4), (30.6) and eq:sum-of-local-invariants (32.13a): for
  (L3/Q, s, a), a = +-prod q^e over the first five inert primes, e <= 2,
  inv_q = j_q v_q(a)/3 with Frob_q = s^(j_q) (Exercise 31.1(i)); the sum
  over these primes is 0 exactly when a = +-1 (mod 7), i.e. when a is a
  local norm at the ramified prime 7.
* (31.8): the Frobenius tau of EW/E generates Gal(W/F) and has order
  m/(m, f) on residue fields (p = 2, 3; f, m <= 4); the identity
  s f' e/m' = (E : K) s/m in Q/Z (exhaustive, small ranges).
* (31.9), (31.10): every quadratic extension of Q_p embeds in the
  quaternion skewfield D_p (p < 30); at 2, Q(2^(1/3)) does not split
  (-1, -1) while Q(2^(1/4)), Q(i) do.
* Exercises 31.2 and 31.4 for quadratic extensions of Q_p, p < 14;
  Exercises 31.5-31.8 on the rational model (Q(i)/Q, s, -1); the local
  index statements of Exercises 29.5, 29.6 at 2.

Not covered: the proofs of (31.7) and (31.11) in general, ramified cyclic
extensions beyond the cubic example, Exercises 31.3, 30.2, 30.3.
"""
from sage.all import (QQ, ZZ, GF, DiagonalQuadraticForm, NumberField,
                      PolynomialRing, QuadraticField, QuaternionAlgebra, gcd,
                      hilbert_symbol, lcm, legendre_symbol, prime_range,
                      set_random_seed, vector)
from functools import reduce
import itertools
import random

set_random_seed(3031)
random.seed(3031)
COUNT = [0]


def ok(condition, what):
    assert condition, what
    COUNT[0] += 1


Rx = PolynomialRing(QQ, 'x')
X = Rx.gen()


class Galois:
    """A Galois number field with its group; index 0 is the identity."""

    def __init__(self, poly, name):
        L = NumberField(poly, name)
        th = L.gen()
        auts = sorted(L.automorphisms(), key=lambda s: s(th) != th)
        self.L, self.th, self.auts, self.n = L, th, auts, len(auts)
        self.imgs = [s(th) for s in auts]
        ok(self.n == L.degree(), 'L/Q is Galois')
        idx = {self.imgs[i]: i for i in range(self.n)}
        self.mult = [[idx[auts[i](auts[j](th))] for j in range(self.n)] for i in range(self.n)]
        self.inv = [[j for j in range(self.n) if self.mult[i][j] == 0][0] for i in range(self.n)]

    def act(self, i, y):
        return self.auts[i](y)

    def rand(self, bound=3):
        while True:
            y = self.L([random.randint(-bound, bound) for _ in range(self.n)])
            if y != 0:
                return y


def coboundary(G, c):
    return [[c[i] * G.act(i, c[j]) / c[G.mult[i][j]] for j in range(G.n)] for i in range(G.n)]


def times(G, f, g):
    return [[f[i][j] * g[i][j] for j in range(G.n)] for i in range(G.n)]


def is_factor_set(G, f):
    return all(G.act(r, f[s][t]) * f[r][G.mult[s][t]] == f[r][s] * f[G.mult[r][s]][t]
               for r in range(G.n) for s in range(G.n) for t in range(G.n))


def normalize(G, f):
    """Exercise 29.1: c_1 = f(1, 1)^(-1), c_s = 1 otherwise."""
    c = [1 / f[0][0]] + [G.L(1)] * (G.n - 1)
    return times(G, coboundary(G, c), f)


def cyclic_factor_set(G, gen, a):
    """(30.1) for a cyclic G with generator index gen; exponents of gen."""
    power = {0: 0}
    k, e = 0, 0
    while True:
        k, e = G.mult[gen][k], e + 1
        if k == 0:
            break
        power[k] = e
    return [[G.L(a) if power[i] + power[j] >= G.n else G.L(1) for j in range(G.n)]
            for i in range(G.n)]


class Crossed:
    def __init__(self, G, f):
        self.G, self.f = G, f

    def mul(self, a, b):
        G, out = self.G, {}
        for i, x in a.items():
            for j, y in b.items():
                k = G.mult[i][j]
                out[k] = out.get(k, 0) + x * G.act(i, y) * self.f[i][j]
        return {k: v for k, v in out.items() if v != 0}

    def vec(self, a):
        return vector(QQ, sum([list(self.G.L(a.get(i, 0))) for i in range(self.G.n)], []))

    def basis(self):
        th = self.G.th
        return [{i: th ** r} for i in range(self.G.n) for r in range(self.G.n)]


def eq(a, b):
    return {k: v for k, v in a.items() if v != 0} == {k: v for k, v in b.items() if v != 0}




def gen_of_cyclic(G):
    for g in range(G.n):
        k, order = g, 1
        while k != 0:
            k, order = G.mult[g][k], order + 1
        if order == G.n:
            return g


def power_of(G, gen, k):
    j, e = 0, 0
    while j != k:
        j, e = G.mult[gen][j], e + 1
    return e


def gal_norm(G, y):
    return reduce(lambda u, v: u * v, [G.act(s, y) for s in range(G.n)])


# --- (30.1): the cyclic factor set -------------------------------------------------

for n in range(1, 31):
    ind = lambda i, j: 1 if i + j >= n else 0
    ok(all(ind(j, k) + ind(i, (j + k) % n) == ind(i, j) + ind((i + j) % n, k)
           for i in range(n) for j in range(n) for k in range(n)),
       'eq:cyclic-factor-set is a factor set (exponents of a), n <= 30')

G3 = Galois(X ** 3 + X ** 2 - 2 * X - 1, 't')
G5 = Galois(X ** 4 + X ** 3 + X ** 2 + X + 1, 'z')      # Q(zeta_5), cyclic of order 4
G7 = Galois(X ** 6 + X ** 5 + X ** 4 + X ** 3 + X ** 2 + X + 1, 'w')   # cyclic of order 6

for G, a in [(G3, 2), (G5, 3), (G7, 5)]:
    g = gen_of_cyclic(G)
    n = G.n
    f = cyclic_factor_set(G, g, a)
    ok(is_factor_set(G, f), '(30.1): (L/K, sigma, a) is a crossed product')
    A = Crossed(G, f)
    u = {g: G.L(1)}
    upow = {0: G.L(1)}
    for j in range(n):
        ok(eq(upow, {[k for k in range(n) if power_of(G, g, k) == j][0]: G.L(1)}),
           '(30.1): u^j = u_(sigma^j) for j < n')
        upow = A.mul(upow, u)
    ok(eq(upow, {0: G.L(a)}), 'eq:cyclic-algebra: u^n = a')
    # (30.2): a normalized factor set g gives (L/K, sigma, prod g(sigma^j, sigma))
    c = [G.rand() for _ in range(n)]
    gfs = normalize(G, times(G, coboundary(G, c), f))
    Ag = Crossed(G, gfs)
    aprime = reduce(lambda x, y: x * y,
                    [gfs[[k for k in range(n) if power_of(G, g, k) == j][0]][g] for j in range(n)])
    ok(aprime in QQ, '(30.2): a = prod_j g(sigma^j, sigma) lies in K^*')
    v = {g: G.L(1)}
    vp = {0: G.L(1)}
    for j in range(n):
        vp = Ag.mul(vp, v)
    ok(eq(vp, {0: aprime}), '(30.2): v_sigma^n = a')
    ok(QQ(aprime) / a == gal_norm(G, c[g]), '(30.3)(iii): a\' = N(c_sigma) a, a norm times a')
    # (30.3)(i): w = u^s, (s, n) = 1
    for s in range(1, n):
        if ZZ(s).gcd(n) != 1:
            continue
        w = {0: G.L(1)}
        for _ in range(s):
            w = A.mul(w, u)
        ws = list(w.keys())[0]
        x = G.rand()
        ok(eq(A.mul(w, {0: x}), A.mul({0: G.act(ws, x)}, w)), '(30.3)(i): w x = sigma^s(x) w')
        wn = {0: G.L(1)}
        for _ in range(n):
            wn = A.mul(wn, w)
        ok(eq(wn, {0: G.L(a) ** s}), '(30.3)(i): w^n = a^s')
    # (30.3)(iii): (c u)^n = N(c) a
    for trial in range(3):
        cc = G.rand()
        cu = {g: cc}
        p_ = {0: G.L(1)}
        for _ in range(n):
            p_ = A.mul(p_, cu)
        ok(eq(p_, {0: gal_norm(G, cc) * a}), '(30.3)(iii): (c u)^n = N(c) a')
    # (30.3)(iv) at the level of factor sets
    fb = cyclic_factor_set(G, g, 7)
    ok(times(G, f, fb) == cyclic_factor_set(G, g, 7 * a), '(30.3)(iv): f_a f_b = f_(ab)')

# (30.4): (L3/Q, sigma, 2) has exponent 3, hence is a skewfield
L3 = G3.L
P2 = L3.ideal(2)
ok(P2.is_prime() and P2.residue_class_degree() == 3, '2 is inert in L3')
ok(L3.disc() == 49 and L3.ring_of_integers().basis() == [1, G3.th, G3.th ** 2],
   'O_L3 = Z[t], discriminant 49')
# v_2(N x) = 3 v_P(x) for x in L3^*, so 2^t is a norm only if 3 | t
for trial in range(30):
    y = G3.rand(6)
    ok(QQ(gal_norm(G3, y)).valuation(2) == 3 * y.valuation(P2), 'v_2(N x) = 3 v_P(x)')
ok(gal_norm(G3, G3.L(2)) == 8, '2^3 = N(2)')
ok(not QQ(2).is_norm(L3) and not QQ(4).is_norm(L3), '2 and 4 are not norms')

# --- (30.6), (30.7): restriction and inflation of the cyclic factor set -----------

for n in range(1, 31):
    for k in [k for k in range(1, n + 1) if n % k == 0]:
        m = n // k
        ind = lambda i, j: 1 if i + j >= n else 0
        b = sum(ind(r * k, k) for r in range(1, m))
        ok(b == 1 or m == 1, '(30.6): b = a')
        ok(all(ind(i * k, j * k) == (1 if i + j >= m else 0) for i in range(m) for j in range(m)),
           '(30.6): f\' is the cyclic factor set of (EL/E, sigma^k, a)')
for n in range(1, 13):
    for s in range(1, 13):
        t = s * n
        ind = lambda i, j: 1 if i + j >= n else 0
        b = sum(ind(j % n, 1 % n) if n > 1 else 1 for j in range(t))
        ok(b == s, '(30.7): b = a^((E : L))')

# --- Exercise 30.1 (B(L/K) = K^*/N(L^*)) and Exercise 30.4 ---------------------------

for d in [-1, 2, 3, 5, -3, -7, 6, -15]:
    Ld = QuadraticField(d, 'r')
    for a in [a for a in range(-30, 31) if a != 0]:
        split = QuaternionAlgebra(QQ, d, a).is_matrix_ring()
        ok(split == QQ(a).is_norm(Ld), '(30.3)(iii), Exercise 30.1: split iff a is a norm')

Ls = QuadraticField(2, 'r')
rt2 = Ls.gen()
unit = 1 + rt2
ok(unit.norm() == -1 and Ls.class_number() == 1 and Ls.disc() == 8 and
   Ls.ring_of_integers().basis() == [1, rt2], 'Exercise 30.4 hint: R = Z[sqrt 2], h = 1, N(1 + sqrt 2) = -1')
Gs = Galois(X ** 2 - 2, 'q')
for p in prime_range(3, 2000):
    qr = legendre_symbol(2, p) == 1
    Ap = Crossed(Gs, cyclic_factor_set(Gs, 1, p))
    if qr:
        P1 = Ls.ideal(p).factor()[0][0]
        alpha = P1.gens_reduced()[0]
        if alpha.norm() == -p:
            alpha = unit * alpha
        ok(alpha.norm() == p, 'Exercise 30.4 hint: p = N(alpha)')
        al = Gs.L(list(alpha))
        uprime = Ap.mul({0: 1 / al}, {1: Gs.L(1)})
        ok(eq(Ap.mul(uprime, uprime), {0: Gs.L(1)}), 'Exercise 30.4: (alpha^-1 u)^2 = 1')
        ok(Ap.mul({0: Gs.L(1), 1: -uprime[1]}, {0: Gs.L(1), 1: uprime[1]}) == {},
           'Exercise 30.4: A has zero divisors, so A = M_2(Q)')
    else:
        if p < 200:
            ok(all((a * a - 2 * b * b) % p != 0 for a in range(p) for b in range(p) if (a, b) != (0, 0)),
               'Exercise 30.4 hint: a^2 = 2 b^2 (mod p) only trivially')
        ok(not QQ(p).is_norm(Ls) and QQ(p * p).is_norm(Ls), 'Exercise 30.4: exp [A] = 2')
        ok(QuaternionAlgebra(QQ, 2, p).is_division_algebra(), 'Exercise 30.4: A is a skewfield')

# --- Section 31 ------------------------------------------------------------------

# norms of finite fields are onto (used through (14.1) in (31.1))
for q, m in [(2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 2), (5, 3),
             (5, 4), (7, 2), (7, 3), (8, 2), (9, 2)]:
    F = GF(q ** m, 'g')
    e = (q ** m - 1) // (q - 1)
    image = {x ** e for x in F if x != 0}
    ok(len(image) == q - 1, '(14.1): N(F_(q^m)^*) = F_q^*')

# (31.4), eq:hasse-invariant and the caution: local invariants of (a, b) = (Q_p(sqrt a)/Q_p, s, b)
# at primes where Q_p(sqrt a)/Q_p is unramified, compared with Hilbert symbols
count_local = 0
for a in [a for a in range(-30, 31) if a not in (0, 1) and ZZ(a).is_squarefree()]:
    for b in [b for b in range(-30, 31) if b != 0]:
        for p in prime_range(32):
            if p == 2:
                if a % 8 != 5 % 8 and a % 8 != 1:
                    continue
                inert = a % 8 == 5
            else:
                if a % p == 0:
                    continue
                inert = legendre_symbol(a, p) == -1
            inv = QQ(ZZ(b).valuation(p)) / 2 if inert else QQ(0)
            inv = inv - inv.floor()
            ok(hilbert_symbol(a, b, p) == (1 if inv == 0 else -1),
               'eq:hasse-invariant: inv = v_p(b)/2 for the Frobenius, 0 if split')
            count_local += 1
ok(count_local > 10000, 'many local cases')

# global reciprocity for (L3/Q, sigma, a): inv at the inert primes from (31.4) and (30.6)
sig = gen_of_cyclic(G3)
th = G3.th
frob = {}
for q in prime_range(50):
    if q == 7:
        continue
    Pq = L3.ideal(q)
    if Pq.is_prime():
        cands = [j for j in [1, 2] if all(c in ZZ for c in
                 list((G3.act([k for k in range(3) if power_of(G3, sig, k) == j][0], th) - th ** q) / q))]
        ok(len(cands) == 1, 'Exercise 31.1(i): Frobenius x -> x^q mod q O_L determines sigma^j')
        frob[q] = cands[0]
        art = L3.galois_group().artin_symbol(L3.prime_above(q))
        ok(art.order() == 3, 'Sage artin symbol has order 3 at an inert prime')
    else:
        ok(q % 7 in (1, 6), 'q splits in L3 iff q = +-1 (mod 7)')
inert = sorted(frob)
ok(inert == [q for q in prime_range(50) if q != 7 and q % 7 not in (1, 6)], 'inert primes')
checked = 0
for combo in itertools.product(range(3), repeat=len(inert[:5])):
    a = reduce(lambda x, y: x * y, [q ** e for q, e in zip(inert[:5], combo)], 1)
    for sgn in [1, -1]:
        aa = sgn * a
        total = sum(QQ(frob[q] * ZZ(aa).valuation(q)) / 3 for q in inert[:5])
        total = total - total.floor()
        local_norm_at_7 = aa % 7 in (1, 6)
        ok((total == 0) == local_norm_at_7,
           'eq:sum-of-local-invariants: sum of inv over unramified primes is 0 iff inv_7 = 0')
        checked += 1
ok(checked == 2 * 3 ** 5, 'all exponent patterns')
ok(all(pow(x, 3, 7) in (1, 6) for x in range(1, 7)) and {pow(x, 3, 7) for x in range(1, 7)} == {1, 6},
   'cubes of (Z/7)^* are +-1 (so units = +-1 mod 7 are 7-adic cubes, hence norms)')

# (31.9), (31.10): every quadratic extension of Q_p embeds in the quaternion skewfield D_p
for p in prime_range(3, 30):
    eps = [x for x in range(2, p) if legendre_symbol(x, p) == -1][0]
    ok(DiagonalQuadraticForm(ZZ, [1, -eps, -p, eps * p]).is_anisotropic(p),
       'D_p = (eps, p) is a skewfield (norm form anisotropic)')
    for c in [eps, p, eps * p]:
        ok(not DiagonalQuadraticForm(ZZ, [eps, p, -eps * p, -c]).is_anisotropic(p),
           '(31.9): Q_p(sqrt c) embeds in D_p')
ok(DiagonalQuadraticForm(ZZ, [1, 1, 1, 1]).is_anisotropic(2), 'D_2 = (-1, -1) is a skewfield')
for c in [3, 5, 7, 2, 6, 10, 14]:
    ok(not DiagonalQuadraticForm(ZZ, [-1, -1, -1, -c]).is_anisotropic(2),
       '(31.9): every quadratic extension of Q_2 embeds in D_2')
# (31.10) globally at 2 for D = (-1, -1): Q(2^(1/3)) does not split D_2, Q(2^(1/4)) does
for poly, splits_at_2 in [(X ** 3 - 2, False), (X ** 4 - 2, True), (X ** 2 + 1, True)]:
    E = NumberField(poly, 'e')
    fin, inf = QuaternionAlgebra(E, -1, -1).ramified_places()
    ok((len([P for P in fin if 2 in P]) == 0) == splits_at_2,
       '(31.10): E splits D_2 iff 2 | (E_P : Q_2) (one prime over 2)')

# Exercise 31.1 on residue fields, and the arithmetic of the proof of (31.8)
for p in [2, 3]:
    for f in range(1, 5):
        for m in range(1, 5):
            N = lcm(f, m)
            F = GF(p ** N, 'h')
            Wf = [x for x in F if x ** (p ** m) == x]          # residue field of W
            Ef = [x for x in F if x ** (p ** f) == x]          # residue field of E
            k = len([x for x in Wf if x ** (p ** f) == x])     # card of residue field of F
            ok(k == p ** gcd(f, m), 'Exercise 31.1(ii): (F : K) = gcd(m, f)')
            kk = gcd(f, m)
            tau_order = min(t for t in range(1, m + 1) if all(x ** (p ** (f * t)) == x for x in Wf))
            ok(tau_order == m // kk,
               '(31.8), Exercise 31.1(iv): tau = sigma^(k f\') generates Gal(W/F), order m\' = m/k')
for s in range(-6, 7):
    for e in range(1, 7):
        for f in range(1, 7):
            for m in range(1, 9):
                d = gcd(m, f)
                mp, fp = m // d, f // d
                lhs = QQ(s * fp * e) / mp
                rhs = QQ(s * e * f) / m
                ok((lhs - rhs) in ZZ, '(31.8): s f\' e / m\' = (E : K) s / m in Q/Z')

# Exercise 31.2 for quadratic extensions: K^*/N(L^*) has order 2
for p in prime_range(14):
    if p == 2:
        reps = [1, -1, 2, -2, 5, -5, 10, -10]
    else:
        eps = [x for x in range(2, p) if legendre_symbol(x, p) == -1][0]
        reps = [1, eps, p, eps * p]
    for d in reps[1:]:
        norms = [b for b in reps if hilbert_symbol(d, b, p) == 1]
        ok(len(norms) * 2 == len(reps), 'Exercise 31.2: [K^* : N(L^*)] = 2 for (L : K) = 2')
    # Exercise 31.4: inv[(L/K, sigma, pi^s)] = s inv[(L/K, sigma, pi)]
    for d in reps[1:]:
        for s in range(6):
            ok(hilbert_symbol(d, p ** s, p) == hilbert_symbol(d, p, p) ** s, 'Exercise 31.4')

# Exercises 31.5-31.8 on the rational model (Q(i)/Q, sigma, -1) of H
Gi = Galois(X ** 2 + 1, 'i')
ok(all(Gi.L([x, y]).norm() >= 0 for x in range(-5, 6) for y in range(-5, 6)),
   'Exercise 31.5: norms from Q(i) (and C) are >= 0, so -1 is not a norm')
ok(QQ(1).is_norm(Gi.L) and not QQ(-1).is_norm(Gi.L), 'Exercise 31.8 hint: t = 2')
Hq = QuaternionAlgebra(QQ, -1, -1)
ok(Hq.is_definite() and Hq.ramified_primes() == [2], '(-1, -1) is ramified at infinity (and 2)')
qs = [Hq(1)] + list(Hq.gens())
ok(all((x * y).conjugate() == y.conjugate() * x.conjugate() for x in qs for y in qs),
   'Exercise 31.8: conjugation is an anti-automorphism, H = H^o, so [H]^2 = [H (x) H^o] = 1')

# Exercises 29.5, 29.6 (local view at 2): D = (L3/Q, sigma, 2), D1 = (-1, -1)
j2 = frob.get(2)
inv2 = QQ(j2) / 3
ok(inv2 in (QQ(1) / 3, QQ(2) / 3), 'inv_2 [D] = j/3 != 0, index 3 at 2')
inv_E = 2 * inv2 - (2 * inv2).floor()
ok(inv_E != 0, 'Exercise 29.5: over Q(i) (ramified quadratic at 2) inv = 2 inv_2 != 0')
tot = QQ(1) / 2 + inv2
ok((tot - tot.floor()).denominator() == 6, 'Exercise 29.6: D1 (x) D has local index 6 at 2')

print('ok s30_31_cyclic_algebras: %d checks' % COUNT[0])
