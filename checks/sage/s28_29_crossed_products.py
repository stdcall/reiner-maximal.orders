"""Exact checks of Sections 28-29: Brauer groups and crossed-product algebras.

Run with `sage -python`. Fields: L3 = Q(t), t^3 + t^2 - 2t - 1 = 0 (cyclic
cubic, conductor 7); L4 = Q(zeta_8) (group C2 x C2); L6 = Q(c), c^6 = -108,
the splitting field of x^3 - 2 (group S3). Crossed products (L/K, f) are
built from the relations (29.1) only: (x u_s)(y u_t) = x s(y) f(s, t) u_(st).
A tensor product C = (L/K, f) (x) (L/K, g) is built on L (x)_Q L =
L[Y]/(m(Y)), m the minimal polynomial of the generator, with
(u_s (x) v_t) z = (s (x) t)(z) (u_s (x) v_t).

Section 28 (pp. 237-241).
* (28.2), th:brauer-group: A (x) A^o -> End_K(A), a (x) b -> (x -> a x b),
  is a homomorphism and bijective for three quaternion algebras and for a
  9-dimensional crossed product over L3 (so [A][A^o] = 1).
* (28.5), (28.10): for D = (-1, -1) and every squarefree d in [-60, 60],
  Q(sqrt d) embeds in D (as its own centralizer) iff it splits D
  (Sage's ramified places of D (x) Q(sqrt d)); for E = Q(sqrt(-7)), which
  does not split D, the centralizer of E in M_2(D) has dimension 8 and
  (E : K)(E' : K) = (M_2(D) : K) (eq:centralizer-dimension-product).
* Exercise 28.1 (E = Q(i, sqrt 2), r = 2) and Exercise 28.2 (two distinct
  subfields Q(X) of M_2(Q) with X^2 = -1, conjugate in M_2(Q)).

Section 29 (pp. 241-259).
* (29.2), eq:factor-set-condition: associativity on basis monomials holds
  for factor sets and fails for a perturbed one; (29.3) the change
  v_s = c_s u_s; Exercise 29.1 (normalization); over L3, L4, L6.
* (29.6) and Exercise 29.2: the center is K and L is its own centralizer
  (L3, L6); (29.8): (L/K, 1) = End_K(L) via x u_s -> x' s (L3, L6); the
  example after (29.8) (L = Q(i), f = -1 gives the quaternions, f = +1 a
  zero divisor).
* (29.9), th:crossed-product-tensor, with the correction C113 of
  eq:idempotent-conjugates (p. 246), over L3 and L6, for all s, t:
  e^2 = e != 0, (x (x) 1) e = (1 (x) x) e (eq:idempotent-diagonal),
  e (u_s (x) v_t) = (u_s (x) v_t)(s^-1 (x) t^-1)(e), the corrected display
  and (29.11), e (u_s (x) v_t) e = 0 for s != t, the w_s multiply by f g,
  and dim_K eCe = n^2 (L3). The printed implicit step e (u_s (x) v_t) =
  (u_s (x) v_t)(s (x) t)(e) is refuted exactly when s^-1 t != s t^-1 (for
  example s != t = 1 in L3); the printed displays themselves agree with the
  true value (both sides vanish for s != t), so the printed text is a wrong
  derivation of true equalities.
* (29.12) proof: Skolem-Noether elements u_s for a conjugate of L3 in
  M_3(Q) give a direct sum and a factor set.
* (29.13): the centralizer of F in (L6/K, f) is the sum of L u_s over
  Gal(L6/F), for F = Q(sqrt(-3)) and F = Q(2^(1/3)).
* (29.16), th:crossed-product-inflation, for (E, L) = (L6, Q(sqrt(-3))) and
  (L4, Q(i)): (29.17) eq:matrix-cocycle, (29.18) eq:matrix-conjugation,
  (29.19), v_s T(x) = T(s x) v_s, v_s v_t = g(s, t) v_(st) with g the
  inflation, B = sum T(E) v_s. Corrections C114 (T is defined on E) and
  C115 (P_sigma in the first display of p. 252) and the question on
  Hom_L(E, E): rho in G - H is not L-linear.
* (29.21), (29.22), eq:schur-matrices: for V = B as left B-module with a
  random L-basis, f(s, t) P(st) = P(s) s(P(t)) and f^m = delta c,
  m = (V : L), over L3 and L6.
* Exercises 29.8-29.12: the standard complex for G = C2, C3, S3 is exact
  at Z, Q_0, Q_1 (and Q_2 for C2, C3); the cochain maps d_i^* = f -> f d_i
  go from Hom(Q_(i-1), M) to Hom(Q_i, M) (Exercise 29.9 as corrected) and
  have the formulas of Exercise 29.10; H^1, H^2 (and H^3 for n <= 3) of
  cyclic groups of order n <= 6 with coefficients in Z/m (m <= 12, every
  action) and in Z agree with (29.29); for F_(q^n)^*, H^1 = H^2 = 0 and
  K^*/N(L^*) = 1 (Exercise 29.13); Exercise 29.11 multiplicatively over L3.
* Exercise 29.14: normal bases of L3, L4, L6.

Not covered: (29.23), (29.24) and Exercises 29.3-29.7 (index statements;
see s30_31_cyclic_algebras.py for local examples), the isomorphism
criterion of (29.6) in general, H^n for n > 3.
"""
from sage.all import (QQ, ZZ, NumberField, PolynomialRing, QuadraticField,
                      QuaternionAlgebra, identity_matrix, matrix, vector,
                      set_random_seed)
from functools import reduce
from math import isqrt
import itertools
import random

set_random_seed(2829)
random.seed(2829)
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


G3 = Galois(X ** 3 + X ** 2 - 2 * X - 1, 't')
G4 = Galois(X ** 4 + 1, 'z')
G6 = Galois(X ** 6 + 108, 'c')
ok(len({tuple(row) for row in G6.mult}) == 6 and any(G6.mult[i][j] != G6.mult[j][i]
   for i in range(6) for j in range(6)), 'Gal(L6/Q) is nonabelian (S3)')


def gen_of_cyclic(G):
    for g in range(G.n):
        k, order = g, 1
        while k != 0:
            k, order = G.mult[g][k], order + 1
        if order == G.n:
            return g


g3 = gen_of_cyclic(G3)


def twisted_factor_set(G, base):
    c = [G.rand() for _ in range(G.n)]
    return normalize(G, times(G, coboundary(G, c), base)), c


# factor sets: cyclic over L3; on C2 x C2 a product of two inflated quaternion
# cocycles is replaced by a random coboundary times a sign cocycle; on S3 the
# inflation of the cyclic factor set of Q(sqrt(-3))/Q.
f3, _ = twisted_factor_set(G3, cyclic_factor_set(G3, g3, 2))
g3fs, _ = twisted_factor_set(G3, cyclic_factor_set(G3, g3, 3))
Lsq = [y for y, _ in (X ** 2 + 3).change_ring(G6.L).roots()]
H6 = [i for i in range(6) if G6.act(i, Lsq[0]) == Lsq[0]]           # Gal(L6/Q(sqrt -3))
Hcube = [i for i in range(6) if G6.act(i, G6.L(1)) == 1 and
         G6.act(i, [y for y, _ in (X ** 3 - 2).change_ring(G6.L).roots()][0]) ==
         [y for y, _ in (X ** 3 - 2).change_ring(G6.L).roots()][0]]
ok(len(H6) == 3 and len(Hcube) == 2, 'subgroups of S3 for Q(sqrt(-3)), Q(2^(1/3))')
infl6 = [[G6.L(-1) if (i not in H6 and j not in H6) else G6.L(1) for j in range(6)] for i in range(6)]
ok(is_factor_set(G6, infl6), '(29.16): the inflated factor set is a factor set')
f6, _ = twisted_factor_set(G6, infl6)
g6fs, _ = twisted_factor_set(G6, [[G6.L(1)] * 6 for _ in range(6)])
f4, _ = twisted_factor_set(G4, [[G4.L(1)] * 4 for _ in range(4)])

# --- (29.2), (29.3), Exercise 29.1 ------------------------------------------------

for G, f in [(G3, f3), (G3, g3fs), (G4, f4), (G6, f6), (G6, g6fs)]:
    ok(is_factor_set(G, f), '(29.2): f is a factor set')
    ok(all(f[0][s] == 1 and f[s][0] == 1 for s in range(G.n)), 'Exercise 29.1: normalized')
    A = Crossed(G, f)
    mons = [{i: G.L(1)} for i in range(G.n)]
    ok(all(eq(A.mul(A.mul(a, b), c), A.mul(a, A.mul(b, c)))
           for a in mons for b in mons for c in mons), '(29.2): associativity on u_s')
    xs = [{i: G.rand()} for i in random.sample(range(G.n), min(3, G.n))]
    ok(all(eq(A.mul(A.mul(a, b), c), A.mul(a, A.mul(b, c)))
           for a in xs for b in xs for c in xs), '(29.2): associativity on x u_s')
    bad = [row[:] for row in f]
    bad[1][1] = 2 * bad[1][1]
    ok(not is_factor_set(G, bad), '(29.2): a perturbed f is not a factor set')
    Ab = Crossed(G, bad)
    ok(not all(eq(Ab.mul(Ab.mul(a, b), c), Ab.mul(a, Ab.mul(b, c)))
               for a in mons for b in mons for c in mons), '(29.2): and not associative')
    c = [G.rand() for _ in range(G.n)]
    dc = coboundary(G, c)
    ok(is_factor_set(G, dc), '(29.3): delta c is a factor set')
    for s in range(G.n):
        for t in range(G.n):
            vs, vt = {s: c[s]}, {t: c[t]}
            ok(eq(A.mul(vs, vt), {G.mult[s][t]: dc[s][t] * f[s][t] * c[G.mult[s][t]]}),
               '(29.3): v_s v_t = (delta c)(s, t) f(s, t) v_st')
    raw = times(G, coboundary(G, [G.rand() for _ in range(G.n)]), f)
    ok(is_factor_set(G, normalize(G, raw)) and
       all(normalize(G, raw)[0][s] == 1 == normalize(G, raw)[s][0] for s in range(G.n)),
       'Exercise 29.1: g = (delta c) f is normalized')

# --- (29.6), Exercise 29.2, (29.8), example --------------------------------------


def lin_map(A, F):
    return matrix(QQ, [A.vec(F(b)) for b in A.basis()])


for G, f in [(G3, f3), (G6, f6)]:
    A = Crossed(G, f)
    th = {0: G.th}
    comm = lambda y: (lambda b: {k: v for k, v in
                                 [(k, A.mul(y, b).get(k, 0) - A.mul(b, y).get(k, 0))
                                  for k in range(G.n)]})
    K_L = lin_map(A, comm(th)).left_kernel()
    ok(K_L.dimension() == G.n and all(A.vec({0: G.th ** r}) in K_L for r in range(G.n)),
       '(29.6): L is its own centralizer')
    Z = K_L
    for s in range(G.n):
        Z = Z.intersection(lin_map(A, comm({s: G.L(1)})).left_kernel())
    ok(Z.dimension() == 1 and A.vec({0: G.L(1)}) in Z, 'Exercise 29.2: the center is K')
    # (29.8): (L/K, 1) = End_K(L)
    triv = [[G.L(1)] * G.n for _ in range(G.n)]
    A1 = Crossed(G, triv)
    pb = [G.th ** r for r in range(G.n)]
    coords = lambda y: vector(QQ, list(G.L(y)))

    def psi(a):
        return matrix(QQ, [coords(sum((x * G.act(i, b) for i, x in a.items()), G.L(0))) for b in pb])
    basis1 = A1.basis()
    ok(matrix(QQ, [psi(b).list() for b in basis1]).rank() == G.n ** 2, '(29.8): psi bijective')
    for a in random.sample(basis1, 6):
        for b in random.sample(basis1, 6):
            # row convention: rows are images of basis vectors, so composition reverses
            ok(psi(A1.mul(a, b)) == psi(b) * psi(a), '(29.8): psi is a homomorphism')

# the example after (29.8): L = Q(i), f(s, s) = -1 gives the rational quaternions
Gi = Galois(X ** 2 + 1, 'i')
for sign in [-1, 1]:
    f = [[Gi.L(1), Gi.L(1)], [Gi.L(1), Gi.L(sign)]]
    A = Crossed(Gi, f)
    u = {1: Gi.L(1)}
    i_ = {0: Gi.th}
    ok(eq(A.mul(u, u), {0: Gi.L(sign)}) and eq(A.mul(u, i_), {1: -Gi.th}),
       'example after (29.8): u^2 = f(s, s), u i = -i u')
    if sign == 1:
        p1, p2 = {0: Gi.L(1), 1: Gi.L(1)}, {0: Gi.L(1), 1: Gi.L(-1)}
        ok(A.mul(p1, p2) == {}, 'example: f(s, s) = +1 gives zero divisors')
    else:
        Bq = QuaternionAlgebra(QQ, -1, -1)
        I, J, _ = Bq.gens()
        to_q = lambda a: sum((Bq(list(x)[0] + list(x)[1] * I) * (J if k == 1 else 1)
                              for k, x in a.items()), Bq(0))
        for a in A.basis():
            for b in A.basis():
                ok(to_q(A.mul(a, b)) == to_q(a) * to_q(b), 'example: A = Q + Qi + Qj + Qk')

# --- (28.2): A (x) A^o = End_K(A) --------------------------------------------------


def sandwich_check(n, mul, basis_vecs, name):
    def M(a, b):
        return matrix(QQ, [mul(mul(a, e), b) for e in basis_vecs])
    mats = [M(a, b).list() for a in basis_vecs for b in basis_vecs]
    ok(matrix(QQ, mats).rank() == n * n, '(28.2): A (x) A^o -> End_K(A) bijective, ' + name)
    for a, b, a2, b2 in [tuple(random.sample(basis_vecs, 4)) for _ in range(8)]:
        # (a (x) b)(a2 (x) b2) = a a2 (x) b2 b in A (x) A^o
        ok(M(mul(a, a2), mul(b2, b)) == M(a2, b2) * M(a, b), '(28.2): homomorphism, ' + name)


for (aa, bb) in [(-1, -1), (2, 5), (-2, -37)]:
    Bq = QuaternionAlgebra(QQ, aa, bb)
    mulq = lambda u, v, Bq=Bq: vector(QQ, (Bq(list(u)) * Bq(list(v))).coefficient_tuple())
    sandwich_check(4, mulq, identity_matrix(QQ, 4).rows(), '(%s, %s)' % (aa, bb))
A3 = Crossed(G3, f3)
B3basis = A3.basis()


def mul3(u, v):
    def unvec(w):
        return {i: G3.L(list(w[3 * i:3 * i + 3])) for i in range(3)}
    return A3.vec(A3.mul(unvec(u), unvec(v)))


sandwich_check(9, mul3, [A3.vec(b) for b in B3basis], '(L3/K, f)')

# --- (28.5), (28.10), Exercises 28.1, 28.2 -----------------------------------------

Bq = QuaternionAlgebra(QQ, -1, -1)
qi, qj, qk = Bq.gens()
for d in [d for d in range(-60, 61) if d not in (0, 1) and ZZ(d).is_squarefree()]:
    E = QuadraticField(d, 'r')
    split = QuaternionAlgebra(E, -1, -1).ramified_places() == ([], [])
    emb = None
    if d < 0:
        for t in range(1, 6):
            for b0, b1, b2 in itertools.product(range(0, isqrt(-d * t * t) + 1), repeat=3):
                if b0 * b0 + b1 * b1 + b2 * b2 == -d * t * t:
                    emb = (b0 * qi + b1 * qj + b2 * qk) / t
                    break
            if emb is not None:
                break
    ok(split == (emb is not None), '(28.5), (28.10): Q(sqrt d) splits D iff it embeds in D')
    ok((emb is not None) == (d < 0 and (-d) % 8 != 7), 'sum of three squares criterion')
    if emb is not None:
        ok(emb ** 2 == d, 'the embedding x^2 = d')
        cent = matrix(QQ, [vector(QQ, (emb * e - e * emb).coefficient_tuple())
                           for e in [Bq(1), qi, qj, qk]]).left_kernel()
        ok(cent.dimension() == 2, '(28.5)(ii): E is its own centralizer in D')

# E = Q(sqrt(-7)) does not split D: its centralizer in M_2(D) has dimension 8


def m2mul(U, V):
    return [U[0] * V[0] + U[1] * V[2], U[0] * V[1] + U[1] * V[3],
            U[2] * V[0] + U[3] * V[2], U[2] * V[1] + U[3] * V[3]]


m2basis = []
for pos in range(4):
    for e in [Bq(1), qi, qj, qk]:
        U = [Bq(0)] * 4
        U[pos] = e
        m2basis.append(U)
flat = lambda U: vector(QQ, sum([list(x.coefficient_tuple()) for x in U], []))
Xm7 = [Bq(0), Bq(-7), Bq(1), Bq(0)]      # [[0, -7], [1, 0]], X^2 = -7
ok(m2mul(Xm7, Xm7) == [Bq(-7), Bq(0), Bq(0), Bq(-7)], 'X^2 = -7 in M_2(Q)')
C = matrix(QQ, [flat(m2mul(Xm7, U)) - flat(m2mul(U, Xm7)) for U in m2basis]).left_kernel()
ok(C.dimension() == 8 and 2 * C.dimension() == 16,
   '(28.5), eq:centralizer-dimension-product: (E : K)(E\' : K) = (B : K)')
ok(QuaternionAlgebra(QuadraticField(-7, 'r'), -1, -1).ramified_places()[0] != [],
   '(28.5): E = Q(sqrt(-7)) does not split D, so E\' > E')
# Exercise 28.1: E = Q(i, sqrt 2) in M_2(D), not in D
Ii = [qi, Bq(0), Bq(0), qi]
S2 = [Bq(0), Bq(2), Bq(1), Bq(0)]
ok(m2mul(Ii, S2) == m2mul(S2, Ii) and m2mul(S2, S2) == [Bq(2), 0, 0, Bq(2)] and
   m2mul(Ii, Ii) == [Bq(-1), 0, 0, Bq(-1)], 'Exercise 28.1: Q(i, sqrt 2) in M_2(D)')
ok(4 > 2, 'Exercise 28.1: (E : K) = 4 exceeds the degree 2 of maximal subfields of D')
# Exercise 28.2: distinct conjugate subfields Q(X), X^2 = -1, of M_2(Q)
X1 = matrix(QQ, [[0, -1], [1, 0]])
X2 = matrix(QQ, [[1, -2], [1, -1]])
ok(X1 ** 2 == -1 and X2 ** 2 == -1, 'Exercise 28.2: X^2 = -1')
ok(matrix(QQ, [identity_matrix(QQ, 2).list(), X1.list(), X2.list()]).rank() == 3,
   'Exercise 28.2: the subfields Q(X1), Q(X2) are different')
g = matrix(QQ, [[1, 1], [0, 1]])
ok(g * X1 * g.inverse() == X2, 'Exercise 28.2: they are conjugate (Skolem-Noether)')

# --- (29.9) with the correction C113 ------------------------------------------------


class Tensor:
    """C = (L/K, f) (x)_K (L/K, g), coefficients in L (x)_Q L = L[Y]/(m(Y))."""

    def __init__(self, G, f, g):
        self.G, self.f, self.g = G, f, g
        TY = PolynomialRing(G.L, 'Y')
        m = TY(list(G.L.defining_polynomial()))
        self.T = TY.quotient(m, 'Yb')
        self.TY = TY
        self.Yimg = [self.one_t(G.imgs[j]) for j in range(G.n)]   # 1 (x) tau(theta)

    def one_t(self, y):
        """1 (x) y."""
        return self.T(self.TY(list(self.G.L(y).polynomial())))

    def t_one(self, x):
        """x (x) 1."""
        return self.T(self.G.L(x))

    def act(self, i, j, z):
        """(s_i (x) s_j)(z)."""
        coeffs = list(z.lift())
        return sum((self.t_one(self.G.act(i, cr)) * self.Yimg[j] ** r
                    for r, cr in enumerate(coeffs)), self.T(0))

    def mul(self, a, b):
        G, out = self.G, {}
        for (i, j), z in a.items():
            for (k, l), w in b.items():
                key = (G.mult[i][k], G.mult[j][l])
                term = z * self.act(i, j, w) * self.t_one(self.f[i][k]) * self.one_t(self.g[j][l])
                out[key] = out.get(key, self.T(0)) + term
        return {k: v for k, v in out.items() if v != 0}

    def vec(self, a):
        G = self.G
        out = []
        for i in range(G.n):
            for j in range(G.n):
                z = a.get((i, j), self.T(0)).lift()
                cs = list(z) + [G.L(0)] * (G.n - len(list(z)))
                for cr in cs:
                    out += list(G.L(cr))
        return vector(QQ, out)


def check_tensor(G, f, g, full_rank):
    C = Tensor(G, f, g)
    L, th, n = G.L, G.th, G.n
    num = reduce(lambda u, v: u * v, [C.t_one(th) - C.one_t(G.imgs[r]) for r in range(1, n)])
    den = reduce(lambda u, v: u * v, [th - G.imgs[r] for r in range(1, n)])
    e = num * C.t_one(1 / den)
    E = {(0, 0): e}
    ok(e != 0 and e * e == e, '(29.9): e is a nonzero idempotent')
    for x in [th, G.rand(), G.rand()]:
        ok(C.t_one(x) * e == C.one_t(x) * e, 'eq:idempotent-diagonal: (x (x) 1) e = (1 (x) x) e')
    inv = G.inv
    wrong_step = set()
    for s in range(n):
        for t in range(n):
            mono = {(s, t): C.T(1)}
            eU = C.mul(E, mono)
            ok(eq(eU, C.mul(mono, {(0, 0): C.act(inv[s], inv[t], e)})),
               '(29.9) (corrected): e (u_s (x) v_t) = (u_s (x) v_t) (s^-1 (x) t^-1)(e)')
            if not eq(eU, C.mul(mono, {(0, 0): C.act(s, t, e)})):
                wrong_step.add((s, t))
            lhs = C.mul(eU, E)
            sinv_a = G.imgs[inv[s]]
            rho = range(1, n)
            brace_c = reduce(lambda u, v: u * v,
                             [C.t_one(sinv_a) - C.one_t(G.imgs[G.mult[inv[t]][r]]) for r in rho]) * \
                C.t_one(1 / reduce(lambda u, v: u * v,
                                   [sinv_a - G.imgs[G.mult[inv[s]][r]] for r in rho]))
            brace_p = reduce(lambda u, v: u * v,
                             [C.t_one(G.imgs[s]) - C.one_t(G.imgs[G.mult[t][r]]) for r in rho]) * \
                C.t_one(1 / reduce(lambda u, v: u * v,
                                   [G.imgs[s] - G.imgs[G.mult[s][r]] for r in rho]))
            ok(brace_c == C.act(inv[s], inv[t], e), 'the corrected brace is (s^-1 (x) t^-1)(e)')
            ok(eq(lhs, C.mul(C.mul(mono, {(0, 0): brace_c}), E)),
               '(29.9): the corrected display before eq:idempotent-conjugates')
            ok(eq(lhs, C.mul(C.mul(mono, {(0, 0): brace_p}), E)),
               '(29.9): the printed display, too, is a true equality')
            fac_c = reduce(lambda u, v: u * v, [sinv_a - G.imgs[G.mult[inv[t]][r]] for r in rho]) / \
                reduce(lambda u, v: u * v, [sinv_a - G.imgs[G.mult[inv[s]][r]] for r in rho])
            fac_p = reduce(lambda u, v: u * v, [G.imgs[s] - G.imgs[G.mult[t][r]] for r in rho]) / \
                reduce(lambda u, v: u * v, [G.imgs[s] - G.imgs[G.mult[s][r]] for r in rho])
            ok(eq(lhs, C.mul(C.mul(mono, E), {(0, 0): C.t_one(fac_c)})),
               'eq:idempotent-conjugates (corrected)')
            ok(eq(lhs, C.mul(C.mul(mono, E), {(0, 0): C.t_one(fac_p)})),
               'eq:idempotent-conjugates (printed) is also a true equality')
            if s != t:
                r0 = G.mult[t][inv[s]]
                ok(r0 != 0 and G.imgs[inv[s]] == G.imgs[G.mult[inv[t]][r0]],
                   '(29.9) (corrected): s^-1 a = t^-1 rho a for rho = t s^-1 != 1')
                r1 = G.mult[inv[t]][s]
                ok(r1 != 0 and G.imgs[s] == G.imgs[G.mult[t][r1]],
                   '(29.9) (printed): s a = t rho a for rho = t^-1 s')
                ok(lhs == {}, '(29.9): e (u_s (x) v_t) e = 0 for s != t')
            else:
                ok(eq(lhs, C.mul(mono, E)) and eq(lhs, eU),
                   '(29.9): e (u_s (x) v_s) e = (u_s (x) v_s) e = e (u_s (x) v_s)')
    expected_wrong = {(s, t) for s in range(n) for t in range(n)
                      if G.mult[inv[s]][t] != G.mult[s][inv[t]]}
    ok(wrong_step == expected_wrong and len(wrong_step) > 0,
       '(29.9) (printed step) e (u_s (x) v_t) = (u_s (x) v_t)(s (x) t)(e) fails iff s^-1 t != s t^-1')
    w = [C.mul({(s, s): C.T(1)}, E) for s in range(n)]
    fg = times(G, f, g)
    for s in range(n):
        for t in range(n):
            ok(eq(C.mul(w[s], w[t]), C.mul(C.mul(C.mul(E, {(0, 0): C.t_one(fg[s][t])}), E),
                                           w[G.mult[s][t]])),
               '(29.9): w_s w_t = e (f g (s, t) (x) 1) e w_st')
        x = G.rand()
        ex = C.mul(C.mul(E, {(0, 0): C.t_one(x)}), E)
        esx = C.mul(C.mul(E, {(0, 0): C.t_one(G.act(s, x))}), E)
        ok(eq(C.mul(w[s], ex), C.mul(esx, w[s])), '(29.9): w_s acts on L\' as s')
    if full_rank:
        basis = [{(i, j): C.t_one(th ** r) * C.one_t(th ** q)}
                 for i in range(n) for j in range(n) for r in range(n) for q in range(n)]
        vecs = [C.vec(C.mul(C.mul(E, b), E)) for b in basis]
        ok(matrix(QQ, vecs).rank() == n * n, '(29.9): (eCe : K) = n^2')
    return wrong_step


ws3 = check_tensor(G3, f3, g3fs, True)
ok((g3, 0) in ws3, '(29.9): the printed step fails for s != t = 1 in L3')
check_tensor(G6, f6, g6fs, False)

# --- (29.12) proof: Skolem-Noether elements for a conjugate of L3 in M_3(Q) -----------

def regular(G, x):
    pb = [G.th ** r for r in range(G.n)]
    return matrix(QQ, [list(G.L(x * b)) for b in pb]).transpose()   # columns: x b_j


gmat = matrix(QQ, 3, 3, [2, 1, 0, 1, 1, 1, 0, 3, 1])
ok(gmat.det() != 0, 'conjugating matrix')
Tg = lambda x: gmat * regular(G3, x) * gmat.inverse()
us = []
for s in range(3):
    # solve u Tg(theta) = Tg(s theta) u
    rows = []
    for a, b in itertools.product(range(3), repeat=2):
        Eab = matrix(QQ, 3, 3, {(a, b): 1})
        rows.append((Eab * Tg(G3.th) - Tg(G3.imgs[s]) * Eab).list())
    sol = matrix(QQ, rows).left_kernel().basis()
    u = sum((random.randint(1, 5) * matrix(QQ, 3, 3, list(v)) for v in sol), matrix(QQ, 3, 3))
    ok(u.det() != 0 and u * Tg(G3.th) * u.inverse() == Tg(G3.imgs[s]),
       '(29.12): u_s x u_s^-1 = s(x) by Skolem-Noether')
    us.append(u)
span = matrix(QQ, [(Tg(G3.th ** r) * us[s]).list() for s in range(3) for r in range(3)])
ok(span.rank() == 9, '(29.12): A = sum L u_s is direct')
fSN = [[None] * 3 for _ in range(3)]
TL = matrix(QQ, [Tg(G3.th ** r).list() for r in range(3)])
for s in range(3):
    for t in range(3):
        F = us[s] * us[t] * us[G3.mult[s][t]].inverse()
        coeff = TL.solve_left(vector(QQ, F.list()))
        fSN[s][t] = G3.L(list(coeff))
        ok(Tg(fSN[s][t]) == F, '(29.12): u_s u_t u_st^-1 lies in L')
ok(is_factor_set(G3, fSN), '(29.12): the u_s define a factor set')

# --- (29.13): centralizer of an intermediate field ------------------------------

A6 = Crossed(G6, f6)
cube = [y for y, _ in (X ** 3 - 2).change_ring(G6.L).roots()][0]
for gamma, H in [(Lsq[0], H6), (cube, Hcube)]:
    comm = lambda b, gamma=gamma: {k: A6.mul({0: gamma}, b).get(k, 0) - A6.mul(b, {0: gamma}).get(k, 0)
                                   for k in range(6)}
    K_F = lin_map(A6, comm).left_kernel()
    expected = matrix(QQ, [A6.vec({s: G6.th ** r}) for s in H for r in range(6)]).row_space()
    ok(K_F == expected, '(29.13): F\' = sum over Gal(L/F) of L u_s')

# --- (29.16): inflation with explicit matrices ------------------------------------


def inflation_check(G, gen_sub, a_value):
    """E = G.L, L = Q(gen_sub) normal in E, Gbar = Gal(L/K) cyclic of order 2."""
    E, n = G.L, G.n
    H = [i for i in range(n) if G.act(i, gen_sub) == gen_sub]
    r, s = len(H), n // len(H)
    ok(s == 2, 'Gal(L/K) of order 2 here')
    Lbasis = [E(1), gen_sub]                       # Q-basis of L
    ebasis = [G.th ** k for k in range(r)]         # candidate L-basis of E
    QB = matrix(QQ, [list(l * e) for e in ebasis for l in Lbasis])
    ok(QB.rank() == n, '(29.16): E = sum L e_i')

    def Lcoords(y):
        """y = sum_i l_i e_i, l_i in L."""
        c = QB.solve_left(vector(QQ, list(E(y))))
        return [c[2 * i] + c[2 * i + 1] * gen_sub for i in range(r)]

    def mat_of(images):
        return matrix(E, [[Lcoords(y)[i] for y in images] for i in range(r)])
    T = lambda x: mat_of([x * e for e in ebasis])
    P = [mat_of([G.act(rho, e) for e in ebasis]) for rho in range(n)]
    apply = lambda sig, M: M.apply_map(lambda z: G.act(sig, z))
    for rho in range(n):
        for sig in range(n):
            ok(P[G.mult[rho][sig]] == P[rho] * apply(rho, P[sig]), 'eq:matrix-cocycle (29.17)')
    for sig in range(n):
        for x in [G.th, G.rand(), G.rand()]:
            ok(T(G.act(sig, x)) * P[sig] == P[sig] * apply(sig, T(x)), 'eq:matrix-conjugation (29.18)')
    for l in Lbasis:
        ok(T(l) == l * identity_matrix(E, r), 'C114: for x in L, T(x) is scalar; T is defined on E')
    Ebasis_Q = [G.th ** k for k in range(n)]
    flatQ = lambda M: vector(QQ, sum([list(z) for z in M.list()], []))
    span = matrix(QQ, [flatQ(T(x) * P[rho]) for x in Ebasis_Q for rho in H])
    ok(span.rank() == r * r * 2, 'eq:matrix-algebra-crossed-product (29.19): M_r(L) = sum T(E) P_rho')
    nonlin = [rho for rho in range(n)
              if any(G.act(rho, gen_sub * e) != gen_sub * G.act(rho, e) for e in ebasis)]
    ok(set(nonlin) == set(range(n)) - set(H), 'rho in G - H is not L-linear (Hom_L(E, E) only for H)')
    # B = sum_{sbar} M_r(L) u_sbar, factor set f on Gbar with f(sbar, sbar) = a
    bar = lambda sig: 0 if sig in H else 1
    fbar = [[E(1), E(1)], [E(1), E(a_value)]]
    sbar_rep = [0, [i for i in range(n) if i not in H][0]]

    def bmul(x, y):
        out = {}
        for i, Mx in x.items():
            for j, My in y.items():
                k = (i + j) % 2
                out[k] = out.get(k, 0) + Mx * apply(sbar_rep[i], My) * fbar[i][j]
        return {k: v for k, v in out.items() if v != 0}
    v = [{bar(sig): P[sig]} for sig in range(n)]
    for sig in range(n):
        for x in [G.th, G.rand()]:
            vT = bmul(v[sig], {0: T(x)})
            ok(eq(vT, {bar(sig): P[sig] * apply(sig, T(x))}),
               'C115: v_s T(x) = P_s s(T(x)) u_sbar')
            ok(eq(vT, bmul({0: T(G.act(sig, x))}, v[sig])), '(29.16): v_s T(x) = T(s x) v_s')
        for tau in range(n):
            gval = fbar[bar(sig)][bar(tau)]
            ok(eq(bmul(v[sig], v[tau]), {bar(G.mult[sig][tau]): gval * P[G.mult[sig][tau]]}),
               '(29.16): v_s v_t = g(s, t) v_st, g the inflation of f')
    flatB = lambda b: vector(QQ, sum([list(flatQ(b.get(k, matrix(E, r, r)))) for k in range(2)], []))
    allB = matrix(QQ, [flatB(bmul({0: T(x)}, v[sig])) for x in Ebasis_Q for sig in range(n)])
    ok(allB.rank() == n * n, 'eq:inflation-basis: B = sum T(E) v_s')
    wrongP = [sig for sig in range(n) for rho in range(n) if rho != sig and
              eq(bmul(v[sig], {0: T(G.th)}), {bar(sig): P[rho] * apply(sig, T(G.th))})]
    ok(wrongP == [], 'C115: the printed P_rho (rho != sigma) gives a different element')


inflation_check(G6, Lsq[0], -1)
iq4 = [y for y, _ in (X ** 2 + 1).change_ring(G4.L).roots()][0]
inflation_check(G4, iq4, 3)

# --- (29.21), (29.22): Schur's matrices --------------------------------------------


def schur_check(G, f):
    A = Crossed(G, f)
    n = G.n
    # V = A as a left A-module; random L-basis v_j = sum_k g_kj u_k
    while True:
        gm = matrix(G.L, n, n, [G.rand(2) for _ in range(n * n)])
        if gm.det() != 0:
            break
    vbasis = [{k: gm[k, j] for k in range(n) if gm[k, j] != 0} for j in range(n)]
    gi = gm.inverse()

    def coords(a):
        """a = sum_i l_i v_i (L acting on the left)."""
        col = vector(G.L, [a.get(k, G.L(0)) for k in range(n)])
        return gi * col
    Pm = []
    for s in range(n):
        Pm.append(matrix(G.L, [list(coords(A.mul({s: G.L(1)}, vj))) for vj in vbasis]).transpose())
    apply = lambda sig, M: M.apply_map(lambda z: G.act(sig, z))
    for s in range(n):
        for t in range(n):
            ok(f[s][t] * Pm[G.mult[s][t]] == Pm[s] * apply(s, Pm[t]), 'eq:schur-matrices (29.21)')
    c = [P.det() for P in Pm]
    fm = [[f[s][t] ** n for t in range(n)] for s in range(n)]
    ok(fm == coboundary(G, c), '(29.22): f^m = delta c, m = (V : L)')


schur_check(G3, f3)
schur_check(G6, f6)

# --- Exercises 29.8-29.13: the standard complex and cohomology -------------------


def perm_group(gens, deg):
    elems = {tuple(range(deg))}
    frontier = list(elems)
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = tuple(g[x[i]] for i in range(deg))
                if y not in elems:
                    elems.add(y)
                    new.append(y)
        frontier = new
    elems = sorted(elems)
    elems.remove(tuple(range(deg)))
    elems = [tuple(range(deg))] + elems
    idx = {e: k for k, e in enumerate(elems)}
    mult = [[idx[tuple(a[b[i]] for i in range(deg))] for b in elems] for a in elems]
    return mult


groups = {'C2': perm_group([(1, 0)], 2), 'C3': perm_group([(1, 2, 0)], 3),
          'S3': perm_group([(1, 0, 2), (1, 2, 0)], 3)}


def bar_matrix(mult, nn):
    """d_nn : Q_nn -> Q_(nn-1) as an integer matrix; Z-basis g[x_1..x_nn]; Q_(-1) = Z."""
    N = len(mult)
    src = list(itertools.product(range(N), repeat=nn + 1))
    if nn == 0:
        return matrix(ZZ, [[1] for _ in src]), src, [()]
    tgt = list(itertools.product(range(N), repeat=nn))
    ti = {t: k for k, t in enumerate(tgt)}
    D = matrix(ZZ, len(src), len(tgt), sparse=True)
    for k, (g, *xs) in enumerate(src):
        terms = [((mult[g][xs[0]],) + tuple(xs[1:]), 1)]
        for i in range(nn - 1):
            merged = tuple(xs[:i]) + (mult[xs[i]][xs[i + 1]],) + tuple(xs[i + 2:])
            terms.append(((g,) + merged, (-1) ** (i + 1)))
        terms.append(((g,) + tuple(xs[:-1]), (-1) ** nn))
        for key, sign in terms:
            D[k, ti[key]] += sign
    return D, src, tgt


for name, mult in groups.items():
    top = 3 if name != 'S3' else 2
    ds = {k: bar_matrix(mult, k)[0] for k in range(top + 1)}
    for k in range(1, top + 1):
        ok((ds[k] * ds[k - 1]).is_zero(), 'Exercise 29.8: d d = 0')
    for k in range(0, top):
        # exactness at Q_k (k >= 0) and at Z: rank d_k + rank d_(k+1) = rank Q_k, image saturated
        rk_k, rk_k1 = ds[k].rank(), ds[k + 1].rank()
        ok(rk_k + rk_k1 == ds[k].nrows(), 'Exercise 29.8: exact at Q_k (ranks)')
        ok(all(d in (0, 1) for d in ds[k + 1].elementary_divisors()),
           'Exercise 29.8: exact at Q_k (image saturated)')
    ok(ds[0].elementary_divisors()[0] == 1, 'Exercise 29.8: d_0 is onto Z')


def cohomology(mult, act, m, top):
    """H^k(G, Z/m) (or Z if m = 0) from the inhomogeneous cochains of Exercise 29.10.

    act[g] is the integer by which g acts. Cochains of degree k are maps G^k -> M,
    (d f)(x_1..x_(k+1)) = x_1 f(x_2..) + sum (-1)^i f(.., x_i x_(i+1), ..) + (-1)^(k+1) f(x_1..x_k).
    """
    N = len(mult)
    dims = [N ** k for k in range(top + 2)]
    cells = [list(itertools.product(range(N), repeat=k)) for k in range(top + 2)]
    index_of = [{c: i for i, c in enumerate(cs)} for cs in cells]
    dmat = []
    for k in range(top + 1):
        Dk = matrix(ZZ, dims[k], dims[k + 1], sparse=True)   # rows: f basis, cols: values
        for col, xs in enumerate(cells[k + 1]):
            Dk[index_of[k][xs[1:]], col] += act[xs[0]]
            for i in range(k):
                merged = xs[:i] + (mult[xs[i]][xs[i + 1]],) + xs[i + 2:]
                Dk[index_of[k][merged], col] += (-1) ** (i + 1)
            Dk[index_of[k][xs[:k]], col] += (-1) ** (k + 1)
        dmat.append(Dk)
    res = []
    for k in range(1, top + 1):
        # cocycles: f with f D_k = 0 mod m; coboundaries: image of D_(k-1) mod m
        Dk, Dp = dmat[k], dmat[k - 1]
        n_k = dims[k]
        Zfree = ZZ ** n_k
        if m == 0:
            cocyc = Dk.dense_matrix().left_kernel()
            cobd = Zfree.submodule(Dp.dense_matrix().rows())
        else:
            big = Dk.dense_matrix().stack(m * identity_matrix(ZZ, Dk.ncols()))
            K = big.left_kernel()
            cocyc = Zfree.submodule([vector(ZZ, list(v)[:n_k]) for v in K.basis()] +
                                    [m * e for e in Zfree.basis()])
            cobd = Zfree.submodule(list(Dp.dense_matrix().rows()) + [m * e for e in Zfree.basis()])
        res.append(cocyc.quotient(cobd).invariants())
    return res


def cyclic_mult(n):
    return [[(i + j) % n for j in range(n)] for i in range(n)]


def order(inv):
    return reduce(lambda u, v: u * v, [x for x in inv], 1) if 0 not in inv else 0


for n in range(2, 7):
    mult = cyclic_mult(n)
    top = 3 if n <= 3 else 2
    for m in range(2, 13):
        for t in range(m):
            if pow(t, n, m) != 1 % m or ZZ(t).gcd(m) != 1:
                continue
            act = [pow(t, k, m) for k in range(n)]
            H = cohomology(mult, act, m, top)
            Nmap = sum(act) % m
            Mprime = [x for x in range(m) if (Nmap * x) % m == 0]
            sm1M = {((t - 1) * x) % m for x in range(m)}
            MG = [x for x in range(m) if ((t - 1) * x) % m == 0]
            NM = {(Nmap * x) % m for x in range(m)}
            h1 = len(Mprime) // len(sm1M)
            h2 = len(MG) // len(NM)
            ok(order(H[0]) == h1, 'eq:cyclic-cohomology: H^1 = M\'/(sigma - 1) M')
            ok(order(H[1]) == h2, 'eq:cyclic-cohomology: H^2 = M^G / N M')
            if top >= 3:
                ok(order(H[2]) == h1, 'eq:cyclic-cohomology: H^3 = H^1')
    H = cohomology(mult, [1] * n, 0, 2)
    ok(H[0] == () and H[1] == (n,), 'eq:cyclic-cohomology with M = Z: H^1 = 0, H^2 = Z/n')
# finite fields: M = F_(q^n)^* = Z/(q^n - 1), sigma = multiplication by q on exponents
for q, n in [(2, 2), (2, 3), (3, 2), (2, 4), (5, 2), (3, 3), (4, 2), (7, 2)]:
    m = q ** n - 1
    act = [pow(q, k, m) for k in range(n)]
    H = cohomology(cyclic_mult(n), act, m, 2)
    ok(H[0] == () and H[1] == (), 'Exercises 29.12, 29.13: H^1 = H^2 = 0 for F_(q^n)/F_q')
    norms = {sum(act) * x % m for x in range(m)}
    ok(len(norms) == q - 1, 'Exercise 29.13: K^*/N(L^*) = 1 (the norm is onto F_q^*)')

# Exercise 29.9 as corrected: d_i^* f = f d_i needs f in Hom(Q_(i-1), M)
for name, mult in groups.items():
    for i in range(1, 3):
        D, src, tgt = bar_matrix(mult, i)
        ok(D.nrows() == len(mult) ** (i + 1) and D.ncols() == len(mult) ** i,
           'd_i : Q_i -> Q_(i-1)')
        ok(D.nrows() != D.ncols(), 'Exercise 29.9 (printed): f in Hom(Q_i, M) cannot be composed with d_i')
# Exercise 29.10: (d^* f) by composition equals the printed formulas (M = Z,
# trivial action and the sign action)


def sign_action(mult):
    N = len(mult)
    act = [1] + [-1 if mult[g][g] == 0 else 1 for g in range(1, N)]
    hom = all(act[mult[a][b]] == act[a] * act[b] for a in range(N) for b in range(N))
    return act if hom else [1] * N


for name, mult in groups.items():
    N = len(mult)
    for act in [[1] * N, sign_action(mult)]:
        for k in range(1, 4):
            D, src, tgt = bar_matrix(mult, k)
            fvals = {c: random.randint(-5, 5) for c in itertools.product(range(N), repeat=k - 1)}
            f_on = lambda key: act[key[0]] * fvals[tuple(key[1:])]
            for col, (g, *xs) in enumerate(src):
                if g != 0:
                    continue
                comp = sum(D[col, j] * f_on(tgt[j]) for j in D.nonzero_positions_in_row(col))
                if k == 1:
                    formula = act[xs[0]] * fvals[()] - fvals[()]
                elif k == 2:
                    x_, y_ = xs
                    formula = act[x_] * fvals[(y_,)] - fvals[(mult[x_][y_],)] + fvals[(x_,)]
                else:
                    x_, y_, z_ = xs
                    formula = (act[x_] * fvals[(y_, z_)] - fvals[(mult[x_][y_], z_)]
                               + fvals[(x_, mult[y_][z_])] - fvals[(x_, y_)])
                ok(comp == formula, 'Exercise 29.10: (d_k^* f) formula')

# Exercise 29.11, multiplicatively over L3: ker d_3^* = factor sets, im d_2^* = delta c
for trial in range(4):
    c = [G3.rand() for _ in range(3)]
    fr = [[G3.rand() for _ in range(3)] for _ in range(3)]
    d3 = lambda f: all(G3.act(x, f[y][z]) / f[G3.mult[x][y]][z] * f[x][G3.mult[y][z]] / f[x][y] == 1
                       for x in range(3) for y in range(3) for z in range(3))
    ok(d3(fr) == is_factor_set(G3, fr), 'Exercise 29.11: d_3^* f = 1 iff f is a factor set')
    ok(d3(coboundary(G3, c)) and d3(f3), 'Exercise 29.11: factor sets lie in ker d_3^*')
    d2 = [[G3.act(x, c[y]) / c[G3.mult[x][y]] * c[x] for y in range(3)] for x in range(3)]
    ok(d2 == coboundary(G3, c), 'Exercise 29.11: d_2^* c = delta c')

# Exercise 29.14: normal bases
for G in [G3, G4, G6]:
    for trial in range(20):
        x = G.rand(2)
        if matrix(QQ, [list(G.act(s, x)) for s in range(G.n)]).rank() == G.n:
            ok(True, 'Exercise 29.14: a normal basis')
            break
    else:
        ok(False, 'Exercise 29.14: no normal basis found')

print('ok s28_29_crossed_products: %d checks' % COUNT[0])
