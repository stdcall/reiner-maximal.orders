"""Global hereditary orders: exact checks of Section 40.

* (40.8) (pp. 370-371) for the hereditary order
  Lambda = {[[a, 6b], [c, d]] : a, b, c, d in ZZ} in M_2(QQ) (local type
  r_2 = r_3 = 2): enumerating every lattice between Lambda and (1/6)Lambda
  (all subgroups of (ZZ/6)^4 invariant under left and right multiplication
  by Lambda) that is a ring, there are exactly (2^2 - 1)^2 = 9 orders
  containing Lambda, 2 * 2 = 4 of them maximal (reduced-trace discriminant
  +-1), namely Gamma_d = [[ZZ, dZZ], [d^-1 ZZ, ZZ]], d | 6, and 2 + 2 = 4
  minimal ones; Gamma^(1,1) cap Gamma^(1,2) cap Gamma^(2,1) = Lambda =
  Gamma^(1,1) cap Gamma^(2,2) (p. 371); every order properly containing
  Lambda is the sum of exactly one set of minimal ones, and not every sum of
  minimal ones is an order.
* (40.9): X(P) = Lambda cap rad Lambda_P (computed from rad(Lambda/P Lambda))
  is a two-sided ideal, X(2)^2 = 2 Lambda, X(3)^2 = 3 Lambda, X(2) X(3) =
  X(3) X(2), and no product X(2)^a X(3)^b, (a, b) != (0, 0) mod 2, is
  c Lambda: Picent Lambda = ZZ/2 x ZZ/2 = prod ZZ/(e_P r_P).
* (40.10) with Lambda' = M_2(ZZ) and P_1 P_2 = 6 Lambda': for X = X(2) X(3),
  L_1 = X Lambda', L_2 = 6 Lambda' X^-1 give the proper factorization
  6 Lambda' = L_2 L_1 and Lambda = O_l(L_1) cap O_l(L_2); Lambda is
  extremal at 2 and 3 ((40.5)).
* (40.6): (X(2) cap X(3))^4 is in 6 Lambda.
* Rosen (40.13), Auslander-Goldman-Rim (40.14), Exercise 40.4 (pp. 373-374,
  379): for the twisted group rings S o G of the quadratic fields QQ(sqrt d),
  d squarefree, |d| <= 30, and of the cyclic cubic fields of conductors 7
  and 9 (S o G realized in End_QQ(L) = M_n(QQ) on an integral basis): at
  each prime p dividing disc(L), S o G is hereditary at p (extremal:
  O_l(Lambda cap rad Lambda_p) = Lambda) iff p is tamely ramified, and it is
  never maximal at p (p divides the discriminant of S o G); at the other
  primes p the discriminant is prime to p (maximal); the trace ideal
  T(S) is ZZ iff every ramified prime is tame (existence of s_0 with
  sum sigma(s_0) = 1); tr(a u_sigma) = T(a) for sigma = 1 and 0 otherwise.

Not established: the general theorems; only the listed orders.
"""
from sage.all import (QQ, ZZ, GF, Integer, NumberField, PolynomialRing,
                      identity_matrix, lcm, matrix, vector)
import itertools

N = 0


def ok(cond, msg=''):
    global N
    assert cond, msg
    N += 1


def lat(rows):
    M = matrix(QQ, [list(r) for r in rows])
    den = M.denominator()
    H = (den * M).change_ring(ZZ).echelon_form(include_zero_rows=False)
    return H.change_ring(QQ) / den


def contains(big, small):
    return all(big.solve_left(v).denominator() == 1 for v in small.rows())


def same(a, b):
    return a.nrows() == b.nrows() and contains(a, b) and contains(b, a)


def lat_cap(a, b):
    d = lcm(a.denominator(), b.denominator())
    M1 = (d * a).change_ring(ZZ).row_module()
    M2 = (d * b).change_ring(ZZ).row_module()
    return M1.intersection(M2).basis_matrix().change_ring(QQ) / d


def radical_mod_p(Ls, e, p):
    """rad(Lambda/p Lambda): Friedl-Ronyai with integer matrices."""
    F = GF(p)
    n = Ls[0].nrows()
    Bs = list(Ls)
    s = 1
    while s <= n and Bs:
        sign = (-1)**s
        data = []
        for b in Bs:
            row = [F(sign * (b * bb).charpoly()[n - s]) for bb in Bs]
            row.append(F(sign * b.charpoly()[n - s]))
            data.append(row)
        C = matrix(F, data).left_kernel().basis()
        Bs = [sum(ZZ(ci) * b for ci, b in zip(c, Bs)) for c in C]
        s *= p
    return [vector(ZZ, [ZZ(c) for c in (b * e)]) for b in Bs]


class Mn:
    def __init__(self, n):
        self.n, self.dim = n, n * n

    def to(self, v):
        return matrix(QQ, self.n, self.n, list(v))

    def fr(self, m):
        return vector(QQ, m.list())

    def mul(self, u, v):
        return self.fr(self.to(u) * self.to(v))

    def one(self):
        return self.fr(identity_matrix(QQ, self.n))

    def std(self):
        return [vector(QQ, [1 if a == b else 0 for b in range(self.dim)])
                for a in range(self.dim)]


def lat_mul(A, L1, L2):
    return lat([A.mul(u, v) for u in L1.rows() for v in L2.rows()])


def dual_solutions(A, conds, target):
    Tinv = target.inverse()
    cols = []
    for f in conds:
        cols += list((matrix(QQ, [f(e) for e in A.std()]) * Tinv).columns())
    W = lat(cols)
    return lat(W.inverse().transpose().rows())


def left_order(A, L):
    return dual_solutions(A, [lambda x, b=b: A.mul(x, b) for b in L.rows()], L)


def right_order(A, L):
    return dual_solutions(A, [lambda x, b=b: A.mul(b, x) for b in L.rows()], L)


def rad_p(A, L, p):
    Ls = [(matrix(QQ, [A.mul(b, c) for c in L.rows()]) * L.inverse()).transpose()
          .change_ring(ZZ) for b in L.rows()]
    e = (A.one() * L.inverse()).change_ring(ZZ)
    rad = radical_mod_p(Ls, e, p)
    return lat([p * r for r in L.rows()] + [vector(QQ, list(v)) * L for v in rad])


def is_ring(A, L):
    Li = L.inverse()
    return all((A.mul(u, v) * Li).denominator() == 1 for u in L.rows() for v in L.rows())


def disc(A, L):
    return matrix(QQ, [[A.to(A.mul(u, v)).trace() for v in L.rows()] for u in L.rows()]).det()


# --- the Eichler order of level 6 -------------------------------------------------
A = Mn(2)


def mono(e11, e12, e21, e22):
    return lat([A.fr(matrix(QQ, 2, 2, {(0, 0): e11})), A.fr(matrix(QQ, 2, 2, {(0, 1): e12})),
                A.fr(matrix(QQ, 2, 2, {(1, 0): e21})), A.fr(matrix(QQ, 2, 2, {(1, 1): e22}))])


Lam = mono(1, 6, 1, 1)
ok(is_ring(A, Lam))
X2, X3 = rad_p(A, Lam, 2), rad_p(A, Lam, 3)
ok(same(X2, mono(2, 6, 1, 2)) and same(X3, mono(3, 6, 1, 3)))
for X, p in [(X2, 2), (X3, 3)]:
    ok(same(lat_mul(A, Lam, X), X) and same(lat_mul(A, X, Lam), X))
    ok(same(lat_mul(A, X, X), lat([p * v for v in Lam.rows()])))
    ok(same(left_order(A, X), Lam) and same(right_order(A, X), Lam))   # extremal at p
ok(same(lat_mul(A, X2, X3), lat_mul(A, X3, X2)))
for a, b in [(1, 0), (0, 1), (1, 1)]:
    Y = Lam
    for _ in range(a):
        Y = lat_mul(A, Y, X2)
    for _ in range(b):
        Y = lat_mul(A, Y, X3)
    idx = abs(Lam.solve_left(Y).det())
    ok(not Integer(idx).nth_root(4, truncate_mode=1)[1])  # [Lambda : c Lambda] = c^4
# (40.6)
R4 = lat_cap(X2, X3)
P = R4
for _ in range(3):
    P = lat_mul(A, P, R4)
ok(contains(lat([6 * v for v in Lam.rows()]), P))
# overorders: Lambda in O in (1/6) Lambda
gensL = [A.to(v) for v in Lam.rows()]
basisL = [A.to(v) for v in Lam.rows()]


def invariant_subspaces(p):
    """F_p-subspaces of (1/p)Lambda / Lambda invariant under Lambda (both sides)."""
    def coords(x):          # x in (1/p) Lambda: coordinates of p x in Lambda, mod p
        return [ZZ(c) % p for c in (A.fr(p * x) * Lam.inverse())]
    W = [m / p for m in basisL]
    maps = []
    for g in gensL:
        maps.append([coords(g * w) for w in W])
        maps.append([coords(w * g) for w in W])
    out = []
    for k in range(5):
        for piv in itertools.combinations(range(4), k):
            free = [(i, j) for i in range(k) for j in range(4) if j > piv[i] and j not in piv]
            for vals in itertools.product(range(p), repeat=len(free)):
                rows = [[0] * 4 for _ in range(k)]
                for i in range(k):
                    rows[i][piv[i]] = 1
                for (i, j), v in zip(free, vals):
                    rows[i][j] = v
                span = {tuple([0] * 4)}
                for row in rows:
                    span = {tuple((a + c * b) % p for a, b in zip(v, row)) for v in span
                            for c in range(p)}
                if all(tuple(sum(row[a] * mp[a][b] for a in range(4)) % p for b in range(4)) in span
                       for mp in maps for row in rows):
                    out.append([sum(c * w for c, w in zip(row, W)) for row in rows])
    return out


orders = []
for S2 in invariant_subspaces(2):
    for S3 in invariant_subspaces(3):
        L = lat(list(Lam.rows()) + [A.fr(x) for x in S2 + S3])
        if is_ring(A, L):
            orders.append(L)
ok(len(orders) == 9, len(orders))
maximal = [O for O in orders if abs(disc(A, O)) == 1]
ok(len(maximal) == 4)
Gd = {d: mono(1, d, QQ(1) / d, 1) for d in [1, 2, 3, 6]}
ok(all(any(same(G, O) for O in maximal) for G in Gd.values()))
minimal = [O for O in orders if not same(O, Lam) and
           not any(not same(O2, Lam) and not same(O2, O) and contains(O, O2) for O2 in orders)]
ok(len(minimal) == 4)
G11, G12, G21, G22 = Gd[1], Gd[3], Gd[2], Gd[6]
ok(same(lat_cap(lat_cap(G11, G12), G21), Lam) and same(lat_cap(G11, G22), Lam))
sums = {}
for k in range(1, 5):
    for Ssub in itertools.combinations(range(4), k):
        L = lat(sum([list(minimal[i].rows()) for i in Ssub], []))
        sums[Ssub] = L
proper = [O for O in orders if not same(O, Lam)]
for O in proper:
    ok(sum(1 for L in sums.values() if same(L, O)) == 1)
ok(any(not is_ring(A, L) for L in sums.values()))
# (40.10)
Lp = Gd[1]
X = lat_mul(A, X2, X3)
Xinv = lat([v / 6 for v in X.rows()])
ok(same(lat_mul(A, X, Xinv), Lam))
L1 = lat_mul(A, X, Lp)
L2 = lat_mul(A, lat([6 * v for v in Lp.rows()]), Xinv)
ok(same(lat_mul(A, L2, L1), lat([6 * v for v in Lp.rows()])))
ok(same(right_order(A, L2), left_order(A, L1)))
ok(same(lat_cap(left_order(A, L1), left_order(A, L2)), Lam))

# --- twisted group rings -------------------------------------------------------------
Rx = PolynomialRing(QQ, 'x')
xx = Rx.gen()
fields = [(xx**2 - d, d) for d in range(-30, 31)
          if d not in (0, 1) and Integer(d).is_squarefree()]
fields += [(xx**3 + xx**2 - 2 * xx - 1, 'C7'), (xx**3 - 3 * xx + 1, 'C9')]
for f, tag in fields:
    K = NumberField(f, 'a')
    n = K.degree()
    S = K.ring_of_integers()
    sb = [K(b) for b in S.basis()]
    autos = K.automorphisms()
    ok(len(autos) == n)                                  # galois

    def mat(a, sigma):
        """matrix of x -> a sigma(x) in the basis sb."""
        Bm = matrix(QQ, [list(b) for b in sb])
        cols = [vector(QQ, list(a * sigma(b))) * Bm.inverse() for b in sb]
        return matrix(QQ, cols).transpose()
    An = Mn(n)
    Lam = lat([An.fr(mat(s, sg)) for s in sb for sg in autos])
    ok(Lam.nrows() == n * n and is_ring(An, Lam))
    dL = K.discriminant()
    dLam = disc(An, Lam)
    traceideal = Integer(0)
    for b in sb:
        traceideal = traceideal.gcd(Integer(b.trace()))
    ram = Integer(dL).prime_divisors()
    tame_all = True
    for p in ram:
        e = K.ideal(p).factor()[0][0].ramification_index()
        tame = e % p != 0
        tame_all = tame_all and tame
        X = rad_p(An, Lam, p)
        hereditary = same(left_order(An, X), Lam)
        ok(hereditary == tame, (tag, p))                 # Rosen (40.13)
        ok(dLam % p == 0, (tag, p))                      # not maximal at p (40.14)
    for p in Integer(dLam).prime_divisors():
        ok(p in ram, (tag, p))                           # maximal away from disc(L)
    ok((traceideal == 1) == tame_all, tag)
    # Exercise 40.4
    for a in sb:
        for sg in autos:
            t = mat(a, sg).trace()
            ok(t == (a.trace() if sg(K.gen()) == K.gen() else 0), tag)

print(f'ok s40_hereditary_global: {N} checks')
