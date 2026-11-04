"""Exact checks of sections 6 (radicals) and 7 (semisimple rings, simple
algebras), pp. 77-107.

Section 6.
  * (6.3), (6.5): for the finite algebras T_2(F_2), T_3(F_2), T_2(F_3)
    (upper triangular matrices), F_2 C_2, F_2 (C_2 x C_2), F_3 C_3 and
    F_2 S_3 the set {x : 1 - a x b is a unit for all a, b} is computed
    exhaustively; it is a nilpotent two-sided ideal and has the expected
    dimension (strictly upper triangular matrices; the augmentation ideal
    for the p-groups; dimension 1 for F_2 S_3).  For the algebras of
    dimension <= 4, all left ideals are enumerated: rad A is the
    intersection of the maximal ones (6.3) and the largest nilpotent left
    ideal (6.9).
  * (6.7) and its proof: x_1^2 - x_1 = 4 n_1^3 - 3 n_1^2 for
    x_1 = x + n_1 - 2 x n_1, n_1 = x^2 - x, identically in Q[x].
  * (6.18), (6.19): the iteration x_(i+1) = x_i + n_i - 2 x_i n_i in
    (Z/5^40)[X]/(X^2 + 1) from x_1 = 3 - X, and in M_2(Z/p^40) from
    x_1 = [[1, 1], [p, 0]] (p = 2, 3, 5): n_i lies in p^(2^(i-1)) A, and the
    limit e is an idempotent lifting the image of x_1.
  * (6.15): for Lambda = Z[X]/(X^p - 1) (the group ring of C_p, localized
    at p) rad Lambda = (p, X - 1) and the least t with
    (rad Lambda)^t in p Lambda is t = p, for p = 2, 3, 5, 7.
  * Exercise 6.9: for the order Lambda = [[Z, Z], [pZ, Z]] (p = 2, 3, 5),
    J = rad Lambda = [[pZ, Z], [pZ, pZ]] satisfies J^2 = p Lambda, and
    J / J^2 contains both simple Lambda / J-modules.
Section 7.
  * (7.1)-(7.3): Q S_3 = Q (+) Q (+) M_2(Q): the central idempotents
    e_chi = chi(1)/6 sum chi(g^(-1)) g are orthogonal, sum to 1, and the
    components have dimensions 1, 1, 4.
  * Exercise 7.10 and its hint: for all groups G of order <= 12 and primes
    p <= 7, the trace form of F_p G is nondegenerate iff p does not divide
    |G| (so F_p G is semisimple, (9.9) argument), and for p | |G| the
    element sum g is a nonzero central nilpotent; nu(1) = n^(-1) sum
    g (x) g^(-1) satisfies mu nu = 1 and (h (x) 1) nu(1) = (1 (x) h) nu(1).
  * (7.11), (7.13): (B : K)(B' : K) = (A : K) and B'' = B for
    B = Q(2^(1/3)) in M_3(Q), B = Q(2^(1/2)) in M_4(Q), B = M_2(Q) (x) 1
    in M_4(Q).
  * (7.15)(i): Q(i) is a maximal subfield of the quaternions (-1, -1)_Q.
  * (7.21), (7.23)(ii): the subfields Q(s), Q(s') of M_2(Q) with
    s^2 = s'^2 = 2 are conjugate; the automorphism s -> -s is inner.
  * Proof of (7.18), case (b): K = F_3(t^3), y = t, F = F_3(t): in
    F (x)_K K(y) = F[Y]/(Y^3 - t^3) the element z = Y - t is a nonzero
    nilpotent, z^3 = 0.
  * Exercises 7.11, 7.12 (with the correction "maximal right ideal" in the
    hint to 7.12): in M_2(F_2), M_2(F_3) every maximal left ideal Ax has a
    complement Ae with e a primitive idempotent; writing 1 = e + a x,
    a x = 1 - e and a x A is a maximal right ideal, not a left ideal (the
    printed "maximal left ideal" is refuted); x A is a maximal right ideal;
    any two maximal left ideals are conjugate; idempotents with
    Ae ~ Ae' are conjugate.
  * Hint to Exercise 7.4 (Milnor's proof): for A = M_n(F_q), (n, q) = (2, 2),
    (2, 3), (3, 2), and the minimal left ideal L of first-column matrices,
    the least m with 1 in L a_1 + ... + L a_m is n, and for such a choice
    L^(m) -> A is bijective.
  * Proof of (7.24): in every group of order <= 24 (GAP SmallGroups) the union
    of the conjugates of a proper subgroup is a proper subset.
What is NOT established: the general theorems.  Matrices over Z/n are
multiplied with integer arithmetic.
"""
from itertools import product

from sage.all import (GF, QQ, ZZ, NumberField, PolynomialRing, SymmetricGroup,
                      CyclicPermutationGroup, PermutationGroup, binomial, gcd, identity_matrix,
                      libgap, matrix, prime_range, set_random_seed,
                      FunctionField)

set_random_seed(20261104)
N = 0


def check(condition, label):
    global N
    assert condition, label
    N += 1


# ------------------------------------------------- finite algebras over F_p
class FinAlg:
    """A finite dimensional F_p-algebra given by structure constants."""

    def __init__(self, p, mult, one):
        self.p = p
        self.dim = len(one)
        self.mult = mult            # mult[i][j] = vector of e_i e_j
        self.one = tuple(one)
        self.elements = list(product(range(p), repeat=self.dim))

    def mul(self, a, b):
        p, d = self.p, self.dim
        out = [0] * d
        for i in range(d):
            if a[i]:
                for j in range(d):
                    if b[j]:
                        c = a[i] * b[j]
                        row = self.mult[i][j]
                        for k in range(d):
                            if row[k]:
                                out[k] += c * row[k]
        return tuple(x % p for x in out)

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple((x - y) % self.p for x, y in zip(a, b))

    def zero(self):
        return tuple([0] * self.dim)

    def units(self):
        units = set()
        for a in self.elements:
            if a in units:
                continue
            for b in self.elements:
                if self.mul(a, b) == self.one and self.mul(b, a) == self.one:
                    units.add(a)
                    units.add(b)
                    break
        return units

    def span(self, gens):
        S = {self.zero()}
        for g in gens:
            S = {self.add(s, tuple((c * x) % self.p for x in g))
                 for s in S for c in range(self.p)}
        return frozenset(S)


def matrix_algebra_upper(n, p):
    idx = [(i, j) for i in range(n) for j in range(i, n)]
    d = len(idx)
    mult = [[[0] * d for _ in range(d)] for _ in range(d)]
    for a, (i, j) in enumerate(idx):
        for b, (k, l) in enumerate(idx):
            if j == k:
                mult[a][b][idx.index((i, l))] = 1
    one = [1 if i == j else 0 for (i, j) in idx]
    return FinAlg(p, mult, one), idx


def group_algebra(G, p):
    els = list(G)
    d = len(els)
    mult = [[[0] * d for _ in range(d)] for _ in range(d)]
    for a, g in enumerate(els):
        for b, h in enumerate(els):
            mult[a][b][els.index(g * h)] = 1
    one = [1 if g == G.identity() else 0 for g in els]
    return FinAlg(p, mult, one), els


def radical_exhaustive(A):
    U = A.units()
    rad = []
    for x in A.elements:
        if all(A.sub(A.one, A.mul(a, x)) in U for a in A.elements):
            rad.append(x)
    return frozenset(rad), U


def is_left_ideal(A, S):
    return all(A.mul(a, s) in S for a in A.elements for s in S)


def is_two_sided(A, S):
    return is_left_ideal(A, S) and all(A.mul(s, a) in S
                                       for a in A.elements for s in S)


def nilpotency(A, S, bound=10):
    cur = set(S)
    for k in range(1, bound + 1):
        if cur == {A.zero()}:
            return k - 1
        cur = A.span([A.mul(a, s) for a in cur for s in S])
        cur = set(cur)
    return None


cases = []
for n, p in [(2, 2), (3, 2), (2, 3)]:
    A, idx = matrix_algebra_upper(n, p)
    strict = frozenset(x for x in A.elements
                       if all(x[k] == 0 for k, (i, j) in enumerate(idx)
                              if i == j))
    cases.append((f'T_{n}(F_{p})', A, strict))
for G, p, dimrad in [(CyclicPermutationGroup(2), 2, 1),
                     (CyclicPermutationGroup(3), 3, 2),
                     (PermutationGroup(['(1,2)', '(3,4)']), 2, 3),
                     (SymmetricGroup(3), 2, 1)]:
    A, els = group_algebra(G, p)
    expected = None
    if G.order() in (2, 3, 4):     # p-groups: the augmentation ideal
        expected = frozenset(x for x in A.elements if sum(x) % p == 0)
    cases.append((f'F_{p}[G], |G| = {G.order()}', A, expected))
    cases[-1] = cases[-1] + (dimrad,)

for case in cases:
    name, A, expected = case[0], case[1], case[2]
    rad, U = radical_exhaustive(A)
    # (6.5) with both a and b, for every x in rad
    check(all(A.sub(A.one, A.mul(A.mul(a, x), b)) in U
              for x in rad for a in A.elements for b in A.elements),
          f'(6.5) {name}')
    check(is_two_sided(A, rad), f'rad is a two-sided ideal {name}')
    k = nilpotency(A, rad)
    check(k is not None, f'(6.9) rad nilpotent {name}')
    if expected is not None:
        check(rad == expected, f'rad = expected {name}')
    if len(case) > 3:
        check(len(rad) == A.p**case[3], f'dim rad {name}')
    # (6.3): intersection of maximal left ideals (dimension dim - 1 or less)
    # computed among all left ideals spanned by at most dim - 1 vectors
    if A.dim <= 4:
        left_ideals = set()
        for r in range(0, A.dim):
            for gens in product(A.elements, repeat=r):
                S = A.span(gens)
                if is_left_ideal(A, S):
                    left_ideals.add(S)
        left_ideals.add(frozenset(A.elements))
        proper = [S for S in left_ideals if len(S) < len(A.elements)]
        maximal = [S for S in proper if not any(S < T for T in proper)]
        inter = frozenset.intersection(*maximal)
        check(inter == rad, f'(6.3) {name}')
        nil = [S for S in left_ideals if nilpotency(A, S) is not None]
        check(all(S <= rad for S in nil) and rad in nil,
              f'(6.9) largest nilpotent left ideal {name}')

# (6.7) identity.
x = PolynomialRing(QQ, 'x').gen()
n1 = x**2 - x
x1 = x + n1 - 2 * x * n1
check(x1**2 - x1 == 4 * n1**3 - 3 * n1**2, '(6.7) identity')
check(x1**2 - x1 == n1**2 * (4 * n1 - 3), '(6.7) n_1^2 divides n_2')

# (6.18) in (Z/5^k)[X]/(X^2 + 1).
q = 5**40


def mul_g(a, b):        # (a0 + a1 X)(b0 + b1 X), X^2 = -1
    return ((a[0] * b[0] - a[1] * b[1]) % q, (a[0] * b[1] + a[1] * b[0]) % q)


def val5(a):
    v = 40
    for c in a:
        c %= q
        if c:
            k = 0
            while c % 5 == 0:
                c //= 5
                k += 1
            v = min(v, k)
    return v


xi = (3, -1 % q)
for i in range(1, 7):
    ni = tuple((u - w) % q for u, w in zip(mul_g(xi, xi), xi))
    check(val5(ni) >= min(40, 2**(i - 1)), '(6.18) n_i in N^(2^(i-1))')
    two_x_n = tuple((2 * c) % q for c in mul_g(xi, ni))
    xi = tuple((u + w - z) % q for u, w, z in zip(xi, ni, two_x_n))
check(mul_g(xi, xi) == xi and (xi[0] - 3) % 5 == 0 and (xi[1] + 1) % 5 == 0,
      '(6.18) limit idempotent lifts 3 - X')


def mmul(a, b, m):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) % m for j in range(2)]
            for i in range(2)]


for p in [2, 3, 5]:
    m = p**40
    xi = [[1, 1], [p, 0]]
    for i in range(1, 8):
        sq = mmul(xi, xi, m)
        ni = [[(sq[r][c] - xi[r][c]) % m for c in range(2)] for r in range(2)]
        vals = [ZZ(e).valuation(p) if e else 40 for row in ni for e in row]
        check(min(vals) >= min(40, 2**(i - 1)), '(6.18) M_2: n_i')
        xn = mmul(xi, ni, m)
        xi = [[(xi[r][c] + ni[r][c] - 2 * xn[r][c]) % m for c in range(2)]
              for r in range(2)]
    check(mmul(xi, xi, m) == xi and xi[0][1] % p == 1 and xi[0][0] % p == 1,
          '(6.18) M_2: idempotent lift')

# (6.15) for Z[X]/(X^p - 1) at p.
for p in [2, 3, 5, 7]:
    R = PolynomialRing(ZZ, 'X')
    X = R.gen()
    for t in range(1, p + 1):
        r = ((X - 1)**t) % (X**p - 1)
        in_p = all(c % p == 0 for c in r.list())
        check(in_p == (t >= p), '(6.15) (rad)^t in p Lambda iff t >= p')

# Exercise 6.9 for the order [[Z, Z], [pZ, Z]].
for p in [2, 3, 5]:
    E = {(i, j): matrix(ZZ, 2, 2, {(i, j): 1}) for i in range(2)
         for j in range(2)}
    Lam = [E[0, 0], E[0, 1], p * E[1, 0], E[1, 1]]
    J = [p * E[0, 0], E[0, 1], p * E[1, 0], p * E[1, 1]]

    def lattice(gens):
        return matrix(ZZ, [g.list() for g in gens]).row_module()
    J2 = lattice([a * b for a in J for b in J])
    check(J2 == lattice([p * g for g in Lam]), 'Exercise 6.9: J^2 = p Lambda')
    check(lattice(J).index_in(lattice(Lam)) == p**2
          and J2.index_in(lattice(J)) == p**2, 'Lambda/J, J/J^2 of order p^2')
    # J/J^2 = span(E_12) + span(p E_21); e_11, e_22 act as the two
    # idempotents of Lambda/J = F_p x F_p.
    check(E[0, 0] * E[0, 1] == E[0, 1] and E[1, 1] * E[0, 1] == 0
          and E[1, 1] * (p * E[1, 0]) == p * E[1, 0]
          and E[0, 0] * (p * E[1, 0]) == 0,
          'Exercise 6.9: both simples in J/J^2')

# ---------------------------------------------------------------- Section 7
G = SymmetricGroup(3)
els = list(G)
chars = G.character_table()
classes = G.conjugacy_classes_representatives()


def class_index(g):
    for k, c in enumerate(classes):
        if g.cycle_type() == c.cycle_type():
            return k


def gmul(a, b):
    out = {}
    for g, cg in a.items():
        for h, ch in b.items():
            out[g * h] = out.get(g * h, 0) + cg * ch
    return {k: v for k, v in out.items() if v != 0}


idem = []
for row in chars.rows():
    deg = row[class_index(G.identity())]
    idem.append({g: QQ(deg) / 6 * QQ(row[class_index(g.inverse())])
                 for g in els})
one = {G.identity(): QQ(1)}
total = {}
for e in idem:
    for g, c in e.items():
        total[g] = total.get(g, 0) + c
check({k: v for k, v in total.items() if v != 0} == one, '(7.1) sum e = 1')
for a in range(3):
    for b in range(3):
        prod_ab = gmul(idem[a], idem[b])
        check(prod_ab == ({k: v for k, v in idem[a].items() if v != 0}
                          if a == b else {}), '(7.1) orthogonal idempotents')
for e in idem:
    for h in els:
        check(gmul({h: 1}, e) == gmul(e, {h: 1}), 'central idempotent')
dims = []
for e in idem:
    vecs = [gmul({h: 1}, e) for h in els]
    M = matrix(QQ, [[v.get(g, 0) for g in els] for v in vecs])
    dims.append(M.rank())
check(sorted(dims) == [1, 1, 4], '(7.2)-(7.3) Q S_3 = Q + Q + M_2(Q)')

# Exercise 7.10 for groups of order <= 12, p <= 7.
groups = []
for n in range(1, 13):
    for i in range(1, int(libgap.NumberSmallGroups(n)) + 1):
        groups.append(libgap.SmallGroup(n, i))
for Gg in groups:
    n = int(Gg.Size())
    elsg = list(Gg.AsList())
    inv = [elsg.index(g.Inverse()) for g in elsg]
    gram = matrix(ZZ, n, n, lambda a, b: n if elsg.index(elsg[a] * elsg[b])
                  == elsg.index(Gg.One()) else 0)
    d = gram.det()
    # sigma = sum g: sigma^2 = n sigma (each k is g h in n ways), and
    # sigma is central (h sigma = sigma = sigma h).
    counts = [0] * n
    for g in elsg:
        for h in elsg:
            counts[elsg.index(g * h)] += 1
    check(all(c == n for c in counts), 'sigma^2 = |G| sigma')
    for p in prime_range(8):
        check((d % p != 0) == (n % p != 0), 'Exercise 7.10 trace form')
    # (h (x) 1) nu(1) = (1 (x) h) nu(1): {(h g, g^(-1))} = {(g', g'^(-1) h)}
    for h in elsg:
        left = sorted((elsg.index(h * g), elsg.index(g.Inverse()))
                      for g in elsg)
        right = sorted((elsg.index(g), elsg.index(g.Inverse() * h))
                       for g in elsg)
        assert left == right
    N += 1

# (7.11), (7.13) centralizers.


def centralizer_dim(gens, n):
    """Dimension of {x in M_n(Q) : x b = b x for all b in gens}."""
    rows = []
    for b in gens:
        for i in range(n):
            for j in range(n):
                row = [0] * (n * n)
                for k in range(n):
                    row[i * n + k] += b[k, j]
                    row[k * n + j] -= b[i, k]
                rows.append(row)
    M = matrix(QQ, rows)
    return n * n - M.rank(), M.right_kernel()


comp = matrix(QQ, [[0, 0, 2], [1, 0, 0], [0, 1, 0]])        # X^3 - 2
d1, ker = centralizer_dim([comp], 3)
check(d1 == 3 and 3 * d1 == 9, '(7.13) (B:K)(B\':K) = (A:K), B = Q(2^(1/3))')
s2 = matrix(QQ, [[0, 2], [1, 0]]).tensor_product(identity_matrix(QQ, 2))
d2, ker2 = centralizer_dim([s2], 4)
check(d2 == 8 and 2 * d2 == 16, '(7.13) B = Q(2^(1/2)) in M_4(Q)')
Bp = [matrix(QQ, 4, 4, list(v)).transpose() for v in ker2.basis()]
Bp = [matrix(QQ, 4, 4, list(v)) for v in ker2.basis()]
d2b, _ = centralizer_dim(Bp, 4)
check(d2b == 2, '(7.11) B\'\' = B')
Ms = [matrix(QQ, 2, 2, {(i, j): 1}).tensor_product(identity_matrix(QQ, 2))
      for i in range(2) for j in range(2)]
d3, ker3 = centralizer_dim(Ms, 4)
check(d3 == 4 and 4 * d3 == 16, '(7.13) B = M_2(Q) (x) 1')
Bp3 = [matrix(QQ, 4, 4, list(v)) for v in ker3.basis()]
check(centralizer_dim(Bp3, 4)[0] == 4, '(7.11) B\'\' = B for M_2(Q) (x) 1')

# (7.15)(i): Q(i) maximal in (-1, -1)_Q: its centralizer has dimension 2.
from sage.all import QuaternionAlgebra
H = QuaternionAlgebra(QQ, -1, -1)
i_, j_, k_ = H.gens()[0], H.gens()[1], H.gens()[0] * H.gens()[1]
basisH = [H(1), i_, j_, k_]
rows = []
for b in basisH:
    c = i_ * b - b * i_
    rows.append(list(c.coefficient_tuple()))
check(4 - matrix(QQ, rows).rank() == 2, '(7.15)(i) Q(i) maximal subfield')

# (7.21), (7.23): conjugate subfields of M_2(Q).
s = matrix(QQ, [[0, 2], [1, 0]])
sp = matrix(QQ, [[1, 1], [1, -1]])
check(s**2 == 2 and sp**2 == 2, 's^2 = s\'^2 = 2')
# solve a s = s' a
rows = []
for r in range(2):
    for c in range(2):
        row = [0] * 4
        for k in range(2):
            row[r * 2 + k] += s[k, c]
            row[k * 2 + c] -= sp[r, k]
        rows.append(row)
sol = matrix(QQ, rows).right_kernel().basis()
a = matrix(QQ, 2, 2, list(sol[0]))
check(a.det() != 0 and a * s * a.inverse() == sp, '(7.23)(ii) conjugate')
u = matrix(QQ, [[1, 0], [0, -1]])
check(u * s * u.inverse() == -s, '(7.23)(i) s -> -s inner')

# (7.18)(b): F (x)_K K(y) = F[Y]/(Y^3 - t^3) has the nilpotent Y - t.
Ft = FunctionField(GF(3), 't')
t = Ft.gen()
RY = PolynomialRing(Ft, 'Y')
Y = RY.gen()
z = Y - t
check((z**3) % (Y**3 - t**3) == 0 and z % (Y**3 - t**3) != 0,
      '(7.18)(b) nonzero nilpotent')
check((Y - t)**3 == Y**3 - t**3, 'Y^3 - t^3 = (Y - t)^3')

# Exercises 7.11, 7.12 and the corrected hint, in M_2(F_q).


def m2(p):
    d = 4
    mult = [[[0] * d for _ in range(d)] for _ in range(d)]
    for a, (i, j) in enumerate([(0, 0), (0, 1), (1, 0), (1, 1)]):
        for b, (k, l) in enumerate([(0, 0), (0, 1), (1, 0), (1, 1)]):
            if j == k:
                mult[a][b][2 * i + l] = 1
    return FinAlg(p, mult, [1, 0, 0, 1])


for p in [2, 3]:
    A = m2(p)
    U = A.units()
    spans = set()
    for u1 in A.elements:
        for u2 in A.elements:
            S = A.span([u1, u2])
            if len(S) == p**2:
                spans.add(S)
    lefts = [S for S in spans if is_left_ideal(A, S)]
    rights = [S for S in spans
              if all(A.mul(s, a) in S for s in S for a in A.elements)]
    check(len(lefts) == p + 1 and len(rights) == p + 1,
          '(16.14)(v) one-sided ideals of M_2(F_p)')
    idems = [e for e in A.elements if A.mul(e, e) == e
             and e not in (A.zero(), A.one)]
    for x in A.elements:
        Ax = frozenset(A.mul(a, x) for a in A.elements)
        if Ax not in lefts:
            continue
        xA = frozenset(A.mul(x, a) for a in A.elements)
        check(xA in rights, 'Exercise 7.12: x A maximal right ideal')
        found = False
        for e0 in idems:
            Ae = frozenset(A.mul(a, e0) for a in A.elements)
            if len(Ae | Ax) == len(Ae) + len(Ax) - 1 and \
                    len(A.span(list(Ae) + list(Ax))) == p**4:
                # A = A e0 (+) A x; write 1 = e + a x with e in A e0
                for e in Ae:
                    r = A.sub(A.one, e)
                    if r in Ax:
                        ax = r
                        break
                check(A.mul(e, e) == e and
                      frozenset(A.mul(a, e) for a in A.elements) == Ae,
                      'decomposition 1 = e + ax, A e = A e0')
                check(A.mul(ax, ax) == ax and ax == A.sub(A.one, e),
                      'a x = 1 - e is idempotent')
                axA = frozenset(A.mul(ax, b) for b in A.elements)
                check(axA in rights, 'corrected hint: a x A maximal right')
                check(axA not in lefts, 'printed "maximal left ideal" refuted')
                found = True
                break
        check(found, 'Exercise 7.12: complement A e')
    # all maximal left ideals conjugate; idempotents of equal rank conjugate
    L0 = lefts[0]
    for L1 in lefts:
        check(any(frozenset(A.mul(A.mul(u, l), next(v for v in U if
                  A.mul(u, v) == A.one)) for l in L0) == L1 for u in U),
              'Exercise 7.12: maximal left ideals conjugate')
    for e in idems:
        for e2 in idems:
            check(any(A.mul(A.mul(u, e), next(v for v in U if
                      A.mul(u, v) == A.one)) == e2 for u in U),
                  'Exercise 7.11: idempotents conjugate')

# Hint to Exercise 7.4.
for n, p in [(2, 2), (2, 3), (3, 2)]:
    rowsF = list(product(range(p), repeat=n))
    nonzero = [r for r in rowsF if any(r)]
    # L a = rank <= 1 matrices v w^T, w = first row of a; sum_i L a_i
    # contains 1 iff the w_i span F_p^n.

    def rank_mod(vectors):
        if not vectors:
            return 0
        return matrix(GF(p), vectors).rank()
    least = min(m for m in range(1, n + 1)
                if any(rank_mod(list(ws)) == n
                       for ws in product(nonzero, repeat=m)))
    check(least == n, 'Milnor: m = n')
    check((p**n)**n == p**(n * n), 'Milnor: card L^(n) = card A')

# (7.24): union of conjugates of a proper subgroup.
for order in range(2, 25):
    for i in range(1, int(libgap.NumberSmallGroups(order)) + 1):
        Gg = libgap.SmallGroup(order, i)
        for cls in Gg.ConjugacyClassesSubgroups():
            Hh = cls.Representative()
            if Hh.Size() == Gg.Size():
                continue
            union = set()
            for K in cls.AsList():
                union.update(str(g) for g in K.AsList())
            assert len(union) < order, ('(7.24)', order, i)
        N += 1

print(f'ok s06_07_radicals_semisimple: {N} checks')
