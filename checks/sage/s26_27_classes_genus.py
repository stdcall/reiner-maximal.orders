"""Exact checks of Sections 26-27: ideal classes, Jordan-Zassenhaus, genus.

Run with `sage -python`. The lattice routines are those of
s21_25_ideal_theory.py (Hermite normal forms of Z-bases in QQ^n). Class sets
of definite quaternion orders over Q come from Sage's `BrandtModule`; they
are used only to pick representatives and the counts h(Lambda).

Section 26 (pp. 225-232).
* (26.5), eq:quaternion-maximal-order: the printed Lambda is an order of
  discriminant 2^2 (maximal by (25.12)) and is Sage's maximal order of
  (-1, -1); u(Lambda) is exactly the 24 printed elements; every x in Lambda
  with coordinates in [-5/2, 5/2] has u x in Z + Zi + Zj + Zk; the euclidean
  step |beta_nu| <= 1/2, nr r < 1 on the grid (Z/6)^4 and x = q y + t,
  nr t < nr y for 200 random pairs; h(Lambda) = 1.
* (26.6), th:four-squares: for every prime p < 60 there are 24(p + 1)
  elements of norm p (24 for p = 2), they give exactly p + 1 maximal left
  ideals Lambda m over p (one for p = 2), nr(Lambda m) = p, and u m is an
  integral quaternion with p = a_0^2 + ... + a_3^2; products of these give
  r = nr(m) for all r < 600 with prime factors < 60; every r <= 2000 is a
  sum of four squares.  The count p + 1 is the number of maximal left
  ideals of M_2(F_p), checked exhaustively for p <= 7 in
  s21_25_ideal_theory.py.
* Exercise 26.1 for Z (|x|, |y| <= 30) and F_2[X], F_3[X] (degree <= 3);
  Exercise 26.2 (100 random 4 x 4 integer matrices); Exercise 26.3 on the
  maximal orders of discriminant 2 and 37.
* Exercise 26.4 as corrected (C108): rank_R M = (L : K) rank_R' M for
  M = Z[i]^3; the printed relation fails.
* Exercise 26.6 as corrected (C109): v(a, b) = (0, r a) has v^2 = 0 and
  M_r / v M_r = Z + Z/rZ (r <= 30); the printed v(a, b) = (0, r b) has
  v^2 != 0.
* Exercise 26.7(i) for Eichler orders of level 2, 3, 5, 7 in the maximal
  orders of discriminant p <= 13; Exercise 26.9 (R = Z[sqrt 2], h(R) = 1,
  2S + 2 sqrt(2) S = 2R has multiplier ring R, hence is not S-isomorphic
  to S).

Section 27 (pp. 232-236).
* (27.6), cor:maximal-orders-matrix-form: Hom_Delta(Delta^(r-1) + J) is the
  printed matrix ring and a maximal order (discriminant d(Delta)^(r^2)),
  for D = 37 with J nonprincipal (r = 2, 3; for r = 3 every row but the last
  is Delta ... Delta J^(-1)) and D = 2 (r = 2).
* (27.1), (27.7): for D = 11, 23, 37, every left ideal class has an integral
  representative M x with [Lambda : M x] prime to I, I in {2, 3, 5, 7, 210,
  D}; then I + ann T = R and M x + I Lambda = Lambda.
* (27.3), (27.4): for two nonprincipal left ideals of the maximal order of
  discriminant 37, the construction of the proof of (27.3) gives
  M_1 + M_2 = s(Lambda) + L' with L' a left ideal; in Z[sqrt(-5)],
  I + J = R(s, t) + IJ(1, 1) for I + J = R.
* Exercise 27.4; Exercise 27.5 and a counterexample to its converse (two
  maximal left ideals over 3 of the Hurwitz order: sum Lambda, norms 9).

Not covered: the Jordan-Zassenhaus theorem itself (finiteness is only seen
in the computed class sets), (26.1)-(26.4) beyond Exercises 26.1-26.4,
Exercises 26.5, 26.7(ii)-(iv), 26.8, (27.2), (27.8), Exercises 27.1-27.3,
27.6, 27.7.
"""
from sage.all import (QQ, ZZ, GF, BrandtModule, Integer, PolynomialRing,
                      QuadraticField, QuaternionAlgebra, block_matrix, factor,
                      gcd, identity_matrix, matrix, prime_range,
                      set_random_seed, vector)
from functools import reduce
from math import isqrt
import itertools
import random

set_random_seed(2675)
random.seed(2675)
COUNT = [0]


def ok(condition, what):
    assert condition, what
    COUNT[0] += 1


# --- Z-lattices in a finite dimensional QQ-algebra -------------------------

class Alg:
    def __init__(self, n, mul, trd):
        self.n, self.mul, self.trd = n, mul, trd
        self.basis = identity_matrix(QQ, n).rows()


def quaternion_alg(B):
    def mul(u, v):
        return vector(QQ, (B(list(u)) * B(list(v))).coefficient_tuple())
    return Alg(4, mul, lambda u: 2 * u[0])


def hnf(rows):
    M = matrix(QQ, rows)
    d = M.denominator()
    H = (d * M).change_ring(ZZ).echelon_form()
    H = H.matrix_from_rows([i for i in range(H.nrows())
                            if not H.row(i).is_zero()])
    return H / d


def dual_cols(C):
    """{x : x * C integral} for a matrix C of full row rank."""
    W = hnf(C.transpose().rows())
    assert W.nrows() == C.nrows()
    return hnf(W.inverse().transpose().rows())


def transporter(maps, N):
    """{x : x * F in N for F in maps}; each F is a linear map (matrix)."""
    Ninv = N.inverse()
    return dual_cols(block_matrix(QQ, 1, len(maps), [F * Ninv for F in maps]))


def rmat(A, b):
    return matrix(QQ, [A.mul(e, b) for e in A.basis])


def lmat(A, b):
    return matrix(QQ, [A.mul(b, e) for e in A.basis])


def O_l(A, M):
    return transporter([rmat(A, b) for b in M.rows()], M)


def O_r(A, M):
    return transporter([lmat(A, b) for b in M.rows()], M)


def prod(A, M, N):
    return hnf([A.mul(a, b) for a in M.rows() for b in N.rows()])


def inverse(A, M):
    """(22.5): M^(-1) = {x : M x subset O_l(M)}."""
    return transporter([lmat(A, b) for b in M.rows()], O_l(A, M))


def contains(M, N):
    return (N * M.inverse()).denominator() == 1


def index(M, N):
    assert contains(M, N)
    return abs(N.det() / M.det())


def disc(A, M):
    return matrix(QQ, [[A.trd(A.mul(a, b)) for b in M.rows()]
                       for a in M.rows()]).det()


def trace_dual(A, M):
    T = matrix(QQ, [[A.trd(A.mul(e, b)) for b in M.rows()] for e in A.basis])
    return dual_cols(T)


def left_ideal(A, Lam, gens):
    return hnf([A.mul(l, g) for l in Lam.rows() for g in gens])


def two_sided(A, Lam, M):
    return O_l(A, M) == Lam and O_r(A, M) == Lam


def rand_elt(M, bound=3):
    while True:
        c = vector(QQ, [random.randint(-bound, bound) for _ in range(M.nrows())])
        if not c.is_zero():
            return c * M


def rand_invertible(M, nr, bound=3):
    while True:
        x = rand_elt(M, bound)
        if nr(x) != 0:
            return x


def setup(D):
    B = QuaternionAlgebra(D)
    A = quaternion_alg(B)
    O = B.maximal_order()
    Lam = hnf([vector(QQ, b.coefficient_tuple()) for b in O.basis()])
    nr = lambda v: B(list(v)).reduced_norm()
    return B, A, Lam, nr


def prime_ideal(A, Lam, nr, p, ramified):
    """frak(P) = Lambda pi + p Lambda (p ramified), p Lambda otherwise."""
    if not ramified:
        return p * Lam
    for c in itertools.product(range(-2, 3), repeat=4):
        x = vector(QQ, c) * Lam
        if nr(x) % p == 0 and nr(x) % (p * p) != 0:
            return left_ideal(A, Lam, [x, p * Lam.row(0)] + [p * r for r in Lam.rows()])
    raise ValueError('no element of norm divisible exactly by p')


def ramified_primes(D):
    return [p for p, _ in factor(D)] if D > 1 else []


def squarefree(D):
    return all(e == 1 for _, e in factor(D)) if D > 1 else True


ALGEBRAS = [1, 2, 3, 5, 6, 10, 13, 15, 22, 37]
SMALL_D = [1, 2, 3, 5, 6, 7, 10, 14, 15]


class MatrixAlgR:
    """M_r(B) acting on columns B^r; coordinates: 4 r^2 and 4 r."""

    def __init__(self, B, r):
        self.B, self.r = B, r
        q = lambda v: B(list(v))

        def split(u, k):
            return [q(u[4 * i:4 * i + 4]) for i in range(k)]

        def join(xs):
            return vector(QQ, sum([list(x.coefficient_tuple()) for x in xs], []))

        def mul(u, v):
            X, Y = split(u, r * r), split(v, r * r)
            return join([sum((X[i * r + k] * Y[k * r + j] for k in range(r)), B(0))
                         for i in range(r) for j in range(r)])

        def act(u, w):
            X, W = split(u, r * r), split(w, r)
            return join([sum((X[i * r + k] * W[k] for k in range(r)), B(0)) for i in range(r)])

        self.alg = Alg(4 * r * r, mul, lambda u: sum(2 * u[4 * (i * r + i)] for i in range(r)))
        self.act, self.join = act, join


def lattice_of(I):
    return hnf([vector(QQ, b.coefficient_tuple()) for b in I.basis()])


def conj_lattice(B, M):
    return hnf([vector(QQ, B(list(r)).conjugate().coefficient_tuple()) for r in M.rows()])


# --- (26.5): the Hurwitz order ----------------------------------------------

B = QuaternionAlgebra(QQ, -1, -1)
A = quaternion_alg(B)
nr = lambda v: B(list(v)).reduced_norm()
one, ii, jj, kk = [vector(QQ, e) for e in identity_matrix(QQ, 4).rows()]
a = (one + ii + jj + kk) / 2
Lam = hnf([one, ii, jj, a])
Lip = hnf([one, ii, jj, kk])
ok(O_l(A, Lam) == Lam and contains(Lam, matrix(QQ, [one])), '(26.5): Lambda is an order')
ok(disc(A, Lam) == -4, '(26.5), (25.12): d(Lambda) = 2^2, so Lambda is maximal')
ok(Lam == lattice_of(B.maximal_order()), '(26.5): the maximal order of (-1, -1)')

halves = [QQ(c) / 2 for c in range(-2, 3)]
units = [vector(QQ, c) for c in itertools.product(halves, repeat=4)
         if contains(Lam, matrix(QQ, [vector(QQ, c)])) and sum(x * x for x in c) == 1]
listed = [s * e for s in [1, -1] for e in [one, ii, jj, kk]] + \
    [vector(QQ, [s0, s1, s2, s3]) / 2 for s0, s1, s2, s3 in itertools.product([1, -1], repeat=4)]
ok(len(units) == 24 and set(map(tuple, units)) == set(map(tuple, listed)),
   '(26.5): u(Lambda) consists of the 24 listed elements')
for u in units:
    uinv = vector(QQ, (B(list(u)) ** -1).coefficient_tuple())
    ok(contains(Lam, matrix(QQ, [uinv])), 'Exercise 25.4: the 24 elements are units')

for c in itertools.product([QQ(x) / 2 for x in range(-5, 6)], repeat=4):
    x = vector(QQ, c)
    if not contains(Lam, matrix(QQ, [x])):
        continue
    ok(any(contains(Lip, matrix(QQ, [A.mul(u, x)])) for u in units),
       '(26.5): u x lies in Z + Zi + Zj + Zk for some unit u')

# the euclidean algorithm: nr(w - q) < 1 for some q in Lambda, w on a grid
N = 6
for c in itertools.product(range(N), repeat=4):
    w = vector(QQ, c) / N
    q = vector(QQ, [round(x) for x in w])           # nearest Lipschitz point
    beta = w - q
    ok(all(abs(b) <= QQ(1) / 2 for b in beta), '(26.5): |beta_nu| <= 1/2')
    if all(abs(b) == QQ(1) / 2 for b in beta):
        ok(contains(Lam, matrix(QQ, [w])), '(26.5): all |beta| = 1/2 gives q in Lambda, r = 0')
        r = vector(QQ, 4)
    else:
        r = beta
    ok(sum(b * b for b in r) < 1, '(26.5): nr r < 1')
for trial in range(200):
    x, y = rand_elt(Lam, 5), rand_elt(Lam, 5)
    w = vector(QQ, (B(list(x)) * B(list(y)) ** -1).coefficient_tuple())
    q = vector(QQ, [round(t) for t in w])
    if all(abs(t) == QQ(1) / 2 for t in w - q):
        q = w
    t = x - A.mul(q, y)
    ok(contains(Lam, matrix(QQ, [q, t])) and nr(t) < nr(y), '(26.5): x = q y + t, nr t < nr y')

ok(len(BrandtModule(2).right_ideals()) == 1, '(26.5): h(Lambda) = 1')

# (26.6): maximal left ideals over p are Lambda m with nr m = p; p = sum of 4 squares


def elements_of_norm(n):
    out = []
    bound = int(isqrt(4 * n)) + 1
    for c in itertools.product(range(-bound, bound + 1), repeat=4):
        if sum(x * x for x in c) == 4 * n and len({x % 2 for x in c}) == 1:
            out.append(vector(QQ, c) / 2)
    return out


for p in prime_range(60):
    elts = elements_of_norm(p)
    ok(len(elts) == (24 if p == 2 else 24 * (p + 1)), 'elements of norm p in Lambda')
    ideals = {}
    for m in elts:
        M = left_ideal(A, Lam, [m])
        ideals[tuple(M.list())] = (M, m)
    ok(len(ideals) == (1 if p == 2 else p + 1),
       '(26.6): p + 1 maximal left ideals Lambda m over p (one if p = 2)')
    for M, m in ideals.values():
        ok(contains(M, p * Lam) and index(Lam, M) == p ** 2,
           '(26.6), (24.13): p Lambda < M < Lambda, nr M = p')
        um = [A.mul(u, m) for u in units if contains(Lip, matrix(QQ, [A.mul(u, m)]))]
        ok(len(um) > 0 and all(sum(x * x for x in v) == p for v in um),
           '(26.6): p = a_0^2 + a_1^2 + a_2^2 + a_3^2')
reps = {}
for p in prime_range(60):
    for m in elements_of_norm(p):
        if all(x in ZZ for x in m):
            reps[p] = m
            break
for r in range(1, 600):
    x = one
    for p, e in factor(r):
        for _ in range(e):
            x = A.mul(x, reps[p]) if p in reps else None
    if x is not None:
        ok(all(t in ZZ for t in x) and nr(x) == r, '(26.6): r = nr of a product of the m_nu')
for r in range(1, 2001):
    ok(any(r - a0 * a0 - a1 * a1 - a2 * a2 >= 0 and isqrt(r - a0 * a0 - a1 * a1 - a2 * a2) ** 2
           == r - a0 * a0 - a1 * a1 - a2 * a2
           for a0 in range(isqrt(r) + 1) for a1 in range(a0 + 1)
           for a2 in range(a1 + 1)), '(26.6): every r is a sum of four squares')

# --- Exercises 26.1-26.3 ---------------------------------------------------------

for x in range(-30, 31):
    for y in range(-30, 31):
        ok(abs(x * y) == abs(x) * abs(y) and abs(x + y) <= abs(x) + abs(y), 'Exercise 26.1(i), Z')
for n in range(1, 200):
    ok(len([x for x in range(-n, n + 1)]) >= n, 'Exercise 26.1(ii), Z')
for q in [2, 3]:
    Rq = PolynomialRing(GF(q), 'X')
    polys = [Rq(list(c)) for d in range(4) for c in itertools.product(range(q), repeat=d + 1)]
    polys = list({str(f): f for f in polys}.values())

    def absval(f):
        return 0 if f == 0 else q ** f.degree()
    for f in polys:
        if f != 0:
            ok(len(set(str(g % f) for g in polys)) == absval(f),
               'Exercise 26.1 hint: card R/R alpha = q^(deg alpha)')
        for g in polys:
            ok(absval(f * g) == absval(f) * absval(g) and absval(f + g) <= absval(f) + absval(g),
               'Exercise 26.1(i), k[X]')
    for n in range(1, 81):
        r = 0
        while q ** (r + 1) <= n:
            r += 1
        count = sum(1 for f in polys if absval(f) <= n)
        if q ** (r + 1) <= len(polys):
            ok(count == q ** (r + 1) and count >= n, 'Exercise 26.1(ii) and hint, k[X]')
for trial in range(100):
    C = matrix(ZZ, 4, 4, [random.randint(-9, 9) for _ in range(16)])
    if C.det() != 0:
        ok(reduce(lambda u, v: u * v, C.elementary_divisors()) == abs(C.det()),
           'Exercise 26.2: card M/N = |det|')
for D in [2, 37]:
    B2, A2, L2, nr2 = setup(D)
    for trial in range(20):
        x = rand_invertible(L2, nr2)
        R = matrix(QQ, [A2.mul(b, x) for b in L2.rows()]) * L2.inverse()
        ok(index(L2, left_ideal(A2, L2, [x])) == abs(R.det()) == nr2(x) ** 2,
           'Exercise 26.3: card Lambda/Lambda x = |N(x)|, right multiplication')

# Exercise 26.4, as corrected: rank_R M = (L : K) rank_R' M for M = Z[i]^3
rank_Rprime, degree = 3, 2
rank_R = matrix(ZZ, 6, 6, 1).rank()  # Z-basis {e_k, i e_k} of Z[i]^3
ok(rank_R == degree * rank_Rprime, 'Exercise 26.4 (corrected): rank_R M = (L : K) rank_R\' M')
ok(rank_Rprime != degree * rank_R, 'Exercise 26.4 (printed): rank_R\' M = (L : K) rank_R M fails')

# Exercise 26.6, as corrected: v(a, b) = (0, r a)
for r in range(1, 31):
    Vc = matrix(ZZ, [[0, 0], [r, 0]])   # columns (a, b) -> (0, r a)
    Vp = matrix(ZZ, [[0, 0], [0, r]])   # printed: (a, b) -> (0, r b)
    ok(Vc * Vc == 0, 'Exercise 26.6 (corrected): v^2 = 0 on M_r')
    if r > 0:
        ok(Vp * Vp != 0, 'Exercise 26.6 (printed): v^2 != 0, M_r not a Lambda-module')
    quotient = ZZ ** 2 / (Vc.column_module())
    ok(quotient.invariants() == ((r, 0) if r > 1 else (0,)),
       'Exercise 26.6: M_r / v M_r = Z + Z/rZ determines r')

# Exercise 26.7(i): Eichler orders Lambda in a maximal order Lambda'
for p in [2, 3, 5, 7, 11, 13]:
    h = len(BrandtModule(p).right_ideals())
    for Nlev in [2, 3, 5, 7]:
        if Nlev != p:
            ok(len(BrandtModule(p, Nlev).right_ideals()) >= h,
               'Exercise 26.7(i): h(Lambda) >= h(Lambda\') for Lambda < Lambda\'')

# Exercise 26.9: R = Z[sqrt 2], S = Z[2 sqrt 2]
L = QuadraticField(2, 's')
ok(L.class_number() == 1 and L.ring_of_integers().basis() == [1, L.gen()],
   'Exercise 26.9: R = Z[sqrt 2] is the maximal order, h(R) = 1')
A2d = Alg(2, lambda u, v: vector(QQ, [u[0] * v[0] + 2 * u[1] * v[1], u[0] * v[1] + u[1] * v[0]]),
          lambda u: 2 * u[0])
S = hnf([vector(QQ, [1, 0]), vector(QQ, [0, 2])])
R = identity_matrix(QQ, 2)
ok(O_l(A2d, S) == S and O_l(A2d, R) == R, 'Exercise 26.9: R and S are Z-orders in L')
Mideal = hnf([2 * r for r in S.rows()] + [A2d.mul(vector(QQ, [0, 2]), r) for r in S.rows()])
ok(Mideal == 2 * R, 'Exercise 26.9: 2S + 2 sqrt(2) S = 2R')
ok(O_l(A2d, Mideal) == R != S, 'Exercise 26.9: its multiplier ring is R, so it is not S x')

# --- Section 27 -----------------------------------------------------------------

# (27.6): the maximal orders of M_r(D), r = 2, 3, with J a nonprincipal right ideal
for p, r in [(37, 2), (37, 3), (2, 2)]:
    Is = BrandtModule(p).right_ideals()
    Bq = Is[0].quaternion_algebra()
    Aq = quaternion_alg(Bq)
    Delta = lattice_of(Is[0].right_order())
    J = lattice_of(Is[-1])
    ok(O_r(Aq, J) == Delta, '(27.6): J is a right Delta-ideal')
    Jinv = inverse(Aq, J)
    Delta1 = O_l(Aq, J)
    MA = MatrixAlgR(Bq, r)
    # M = Delta^(r-1) + J as a lattice of columns
    cols = []
    for k in range(r):
        part = J if k == r - 1 else Delta
        for d in part.rows():
            w = [vector(QQ, 4)] * r
            w[k] = d
            cols.append(vector(QQ, sum([list(x) for x in w], [])))
    M = hnf(cols)
    E = identity_matrix(QQ, 4 * r * r).rows()
    maps = [matrix(QQ, [MA.act(e, m) for e in E]) for m in M.rows()]
    End = transporter(maps, M)
    blocks = []
    for i in range(r):
        for j in range(r):
            ent = Delta if (i < r - 1 and j < r - 1) else (
                Jinv if i < r - 1 else (J if j < r - 1 else Delta1))
            for d in ent.rows():
                w = [vector(QQ, 4)] * (r * r)
                w[i * r + j] = d
                blocks.append(vector(QQ, sum([list(x) for x in w], [])))
    ok(End == hnf(blocks), '(27.6): Hom_Delta(Delta^(r-1) + J) is the printed matrix ring')
    ok(O_l(MA.alg, End) == End, '(27.6): it is an order')
    ok(abs(disc(MA.alg, End)) == abs(disc(Aq, Delta)) ** (r * r),
       '(27.6): it is maximal (discriminant of M_r(Delta))')
    if p == 37:
        ok(len(Is) == 3, 'h = 3 for D = 37: J is taken from a nonprincipal class')

# (27.1), (27.7): integral representatives relatively prime to N
for p in [11, 23, 37]:
    Is = BrandtModule(p).right_ideals()
    Bq = Is[0].quaternion_algebra()
    Aq = quaternion_alg(Bq)
    nrq = lambda v, Bq=Bq: Bq(list(v)).reduced_norm()
    O = lattice_of(Is[0].right_order())
    for Jr in Is:
        M = conj_lattice(Bq, lattice_of(Jr))   # a left O-ideal
        ok(O_l(Aq, M) == O, '(27.7): conjugates of right ideals are left ideals')
        Mi = inverse(Aq, M)
        for I in [2, 3, 5, 7, 210, p]:
            found = False
            for trial in range(400):
                x = rand_elt(Mi, 2)
                if nrq(x) == 0:
                    continue
                Mx = hnf([Aq.mul(m, x) for m in M.rows()])
                if contains(O, Mx) and gcd(index(O, Mx), I) == 1:
                    found = True
                    T_exponent = max(d for d in (Mx * O.inverse()).change_ring(ZZ).elementary_divisors())
                    ok(gcd(T_exponent, I) == 1, '(27.1): I + ann_R T = R')
                    ok(hnf(Mx.rows() + [I * b for b in O.rows()]) == O,
                       '(27.7): M x + N = Lambda, N = I Lambda')
                    break
            ok(found, '(27.7): an integral ideal in the class prime to N')

# (27.3), (27.4): M_1 + M_2 = Lambda + L' for two nonprincipal left ideals (D = 37)
Is = BrandtModule(37).right_ideals()
Bq = Is[0].quaternion_algebra()
Aq = quaternion_alg(Bq)
nrq = lambda v: Bq(list(v)).reduced_norm()
O = lattice_of(Is[0].right_order())
M1 = conj_lattice(Bq, lattice_of(Is[1]))
M2 = conj_lattice(Bq, lattice_of(Is[2]))


def embed_prime_to(M, I):
    Mi = inverse(Aq, M)
    while True:
        x = rand_elt(Mi, 2)
        if nrq(x) != 0:
            Mx = hnf([Aq.mul(m, x) for m in M.rows()])
            if contains(O, Mx) and gcd(index(O, Mx), I) == 1:
                return Mx


P1 = embed_prime_to(M1, 1)
P2 = embed_prime_to(M2, index(O, P1))
ok(hnf(P1.rows() + P2.rows()) == O, '(27.3), Exercise 27.5: phi(M_1) + psi(M_2) = Lambda')
Mz = (P1.stack(P2) * O.inverse()).change_ring(ZZ)
H, U = Mz.echelon_form(transformation=True)
ok(H.matrix_from_rows(range(4)) == identity_matrix(ZZ, 4), '(27.3): the sum is Lambda')
target = (vector(QQ, [1, 0, 0, 0]) * O.inverse()).change_ring(ZZ)
coeffs = vector(ZZ, list(target) + [0] * 4) * U
ok(coeffs * Mz == target, '(27.3): 1 as a combination')
a0 = vector(QQ, list(coeffs[:4])) * P1
b0 = vector(QQ, list(coeffs[4:])) * P2
ok(a0 + b0 == vector(QQ, [1, 0, 0, 0]), '(27.3): 1 = a_0 + b_0, a_0 in phi(M_1), b_0 in psi(M_2)')
Lp = dual_cols(hnf(dual_cols(P1.transpose()).rows() + dual_cols(P2.transpose()).rows()).transpose())
ok(contains(P1, Lp) and contains(P2, Lp) and O_l(Aq, Lp) == O, '(27.3): L\' = kernel is a left ideal')
section = [vector(QQ, list(Aq.mul(l, a0)) + list(Aq.mul(l, b0))) for l in O.rows()]
kernel = [vector(QQ, list(c) + list(-c)) for c in Lp.rows()]
direct = hnf([vector(QQ, list(r) + [0] * 4) for r in P1.rows()] +
             [vector(QQ, [0] * 4 + list(r)) for r in P2.rows()])
ok(hnf(section + kernel) == direct and matrix(QQ, section + kernel).rank() == 8,
   '(27.3), (27.4): M_1 + M_2 = s(Lambda) + L\' (direct), so M_1 + M_2 = Lambda + L\'')

# (27.4) in a commutative maximal order: Z[sqrt(-5)]
K5 = QuadraticField(-5, 'w')
w = K5.gen()
OK = K5.ring_of_integers()
ok(K5.class_number() == 2, 'Z[sqrt(-5)] has class number 2')
I = K5.ideal(2, 1 + w)
J = K5.ideal(3, 1 + w)
ok(not I.is_principal() and not J.is_principal() and (I * J).is_principal(), 'I, J, IJ')
ok(I + J == K5.ideal(1), 'I + J = R')
# I + J = R (s, t) + IJ (1, 1) with s in I, t in J, s - t = 1
for s_ in [x for x in [K5(c0) + c1 * w for c0 in range(-6, 7) for c1 in range(-3, 4)] if x in I]:
    if s_ - 1 in J:
        t_ = s_ - 1
        break
ok(s_ in I and t_ in J and s_ - t_ == 1, '(27.4): s - t = 1')


def zrows(ideal):
    return [vector(QQ, list(K5(b))) for b in ideal.basis()]


IJ = I * J
lhs = hnf([vector(QQ, list(x) + [0, 0]) for x in zrows(I)] +
          [vector(QQ, [0, 0] + list(y)) for y in zrows(J)])
rhs = hnf([vector(QQ, list(c * s_) + list(c * t_)) for c in [K5(1), w]] +
          [vector(QQ, list(z) + list(z)) for z in [K5(list(v)) for v in zrows(IJ)]])
ok(lhs == rhs, '(27.4): I + J = R + IJ in Z[sqrt(-5)]')

# Exercise 27.4: ord_R Lambda/M subset M
for D in [2, 6, 37]:
    B3, A3, L3, nr3 = setup(D)
    for trial in range(10):
        M = left_ideal(A3, L3, [rand_invertible(L3, nr3), rand_invertible(L3, nr3)])
        ok(contains(M, index(L3, M) * L3), 'Exercise 27.4: ord Lambda/M subset M')
        M2 = left_ideal(A3, L3, [rand_invertible(L3, nr3)])
        if gcd(index(L3, M), index(L3, M2)) == 1:
            ok(hnf(M.rows() + M2.rows()) == L3, 'Exercise 27.5: coprime norms give M_1 + M_2 = Lambda')
# Exercise 27.5, the converse fails: two maximal left ideals over 3 in the Hurwitz order
over3 = []
for m in elements_of_norm(3):
    M = left_ideal(A, Lam, [m])
    if all(M != X for X in over3):
        over3.append(M)
ok(len(over3) == 4 and hnf(over3[0].rows() + over3[1].rows()) == Lam and
   gcd(index(Lam, over3[0]), index(Lam, over3[1])) == 9,
   'Exercise 27.5: M_1 + M_2 = Lambda although both norms are 9')

print('ok s26_27_classes_genus: %d checks' % COUNT[0])
