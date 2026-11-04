"""Picard groups of maximal orders: exact checks of Section 37 (and of
Exercises 38.3, 38.5).

* (37.32)-(37.33) (p. 333) for quaternion algebras over QQ: for a maximal
  order O of discriminant D, D squarefree, 1 < D < 100, the two-sided prime
  P_p over p | D (P_p / pO = radical of the reduced trace form mod p)
  satisfies P_p^2 = pO, and no product of distinct P_p is of the form cO
  (its reduced norm is not a square): Picent O = (ZZ/2)^w(D), as
  1 -> Cl ZZ = 1 -> Picent O -> prod_(p | D) ZZ/m_p -> 1 with m_p = 2.
* (37.25), (37.34) (pp. 327, 334): for indefinite D < 50 (Eichler condition)
  every P_p = O x_p with x_p in the normalizer N(O) (x_p O x_p^-1 = O,
  nr x_p = +-p not +- a square), so omega' : N(O)/u(O)QQ^* -> Picent O is
  onto and ker theta = Picent O = Outcent O (Cl O = 1).
  Without the Eichler condition (Remark (37.41)): for every prime D < 200
  and every type O_i of maximal orders of the definite algebra (left orders
  of the Brandt right ideals), P_D is principal iff O_i contains an element
  of reduced norm D; for D in a nonempty list of cases it is not, so
  ker theta = Picent O_i = ZZ/2 while im omega = 1: (37.34) fails there.
  For D = 2 (the order ZZ + ZZi + ZZj + ZZ(1 + i + j + k)/2 of Section 26
  cited in Remark (37.41), maximal: discriminant 4 = D^2) there is one ideal
  class, so (37.43) holds although the Eichler condition does not.
* (37.40)(ii) (p. 337) for R = ZZ[sqrt -5] (Cl R = ZZ/2) and
  R = ZZ[sqrt -14] (Cl R = ZZ/4, (Cl R)_2 = ZZ/2), n = 2: for an ideal a
  with a^2 principal and [a] != 1 of order 2, an explicit x in GL_2(K) with
  R^2 x = a + a satisfies x^-1 M_2(R) x = M_2(R), x is not in
  K^* GL_2(R) (so i_x is an outer automorphism), and x^2 / c is in GL_2(R)
  for a^2 = cR (so i_x^2 is inner).
* Exercises 38.3 and 38.5 (p. 349) for R = ZZ: every x in M_2(ZZ) with
  entries in [-5, 5] and det x != 0 such that x M_2(ZZ) x^-1 is in M_2(ZZ)
  satisfies x M_2(ZZ) x^-1 = M_2(ZZ) and x / content(x) in GL_2(ZZ);
  the ZZ[sqrt -5] example above shows that the PID hypothesis is needed.

Not established: the exact sequences in general; only the listed orders.
"""
from sage.all import (QQ, ZZ, GF, Integer, BrandtModule, QuadraticField,
                      QuadraticForm, QuaternionAlgebra, gcd, hilbert_symbol,
                      identity_matrix, matrix, prime_range, vector)
import itertools
from math import isqrt

N = 0


def ok(cond, msg=''):
    global N
    assert cond, msg
    N += 1


def ramified(a, b):
    places = [-1] + sorted(set(Integer(2 * a * b).prime_divisors()))
    return [v for v in places if hilbert_symbol(a, b, v) == -1]


def algebra_with_discriminant(D):
    primes = Integer(D).prime_divisors()
    if len(primes) % 2 == 1:
        return QuaternionAlgebra(D), None
    for a in [-1, -2, -3, -5, -6, -7, -10, -11, -13, 2, 3, 5]:
        for b in list(range(-200, 0)) + list(range(2, 200)):
            if Integer(b).is_squarefree():
                ram = ramified(a, b)
                if -1 not in ram and ram == primes:
                    return QuaternionAlgebra(QQ, a, b), (a, b)
    raise ValueError(D)


def lattice(rows):
    M = matrix(QQ, rows)
    den = M.denominator()
    H = (den * M).change_ring(ZZ).echelon_form(include_zero_rows=False)
    return H.change_ring(QQ) / den


def contains(big, small):
    return all(big.solve_left(v).denominator() == 1 for v in small.rows())


def same(L1, L2):
    return L1.nrows() == L2.nrows() and contains(L1, L2) and contains(L2, L1)


def find_norm(B, ab, rows, targets, bound):
    """An element of the lattice with reduced norm in targets (indefinite B)."""
    a, b = ab
    els = [B(list(r)) for r in rows]
    W = matrix(QQ, [[1, 0, 0, 0], [0, abs(a), 0, 0], [0, 0, abs(b), 0],
                    [0, 0, 0, abs(a * b)]])
    M = matrix(QQ, [list(r) for r in rows])
    G = M * W * M.transpose()
    U = (G.denominator() * G).change_ring(ZZ).LLL_gram()
    red = [sum(U[j, i] * els[j] for j in range(4)) for i in range(4)]
    Q = matrix(QQ, 4, 4, lambda i, j: (red[i] * red[j].conjugate()).reduced_trace() / 2)
    d = int(Q.denominator())
    Qi = [[int(d * Q[i, j]) for j in range(4)] for i in range(4)]
    A2 = Qi[0][0]
    for c1, c2, c3 in itertools.product(range(-bound, bound + 1), repeat=3):
        cc = (c1, c2, c3)
        B1 = 2 * (Qi[0][1] * c1 + Qi[0][2] * c2 + Qi[0][3] * c3)
        C0 = sum(Qi[i + 1][j + 1] * cc[i] * cc[j] for i in range(3) for j in range(3))
        for t in targets:
            disc = B1 * B1 - 4 * A2 * (C0 - d * int(t))
            if disc < 0 or isqrt(disc)**2 != disc:
                continue
            for num in (-B1 + isqrt(disc), -B1 - isqrt(disc)):
                if num % (2 * A2) == 0:
                    x = (num // (2 * A2)) * red[0] + c1 * red[1] + c2 * red[2] + c3 * red[3]
                    if x.reduced_norm() == t:
                        return x
    return None


def two_sided_prime(basis, p):
    gram = matrix(ZZ, [[(x * y).reduced_trace() for y in basis] for x in basis])
    ker = gram.change_ring(GF(p)).right_kernel().basis()
    return lattice([list(p * x) for x in basis] +
                   [list(sum(ZZ(c) * b for c, b in zip(v, basis))) for v in ker])


# --- Picent of maximal quaternion orders --------------------------------------
for D in [d for d in range(2, 100) if Integer(d).is_squarefree()]:
    B, ab = algebra_with_discriminant(D)
    O = B.maximal_order()
    basis = list(O.basis())
    Ol = lattice([list(x) for x in basis])

    def prod_lat(L1, L2):
        return lattice([list(B(list(u)) * B(list(v))) for u in L1.rows() for v in L2.rows()])

    primes = Integer(D).prime_divisors()
    Ps = {p: two_sided_prime(basis, p) for p in primes}
    for p, P in Ps.items():
        ok(same(prod_lat(Ol, P), P) and same(prod_lat(P, Ol), P))     # two-sided
        ok(same(prod_lat(P, P), lattice([list(p * x) for x in basis])))  # P^2 = pO
    for r in range(1, len(primes) + 1):
        for S in itertools.combinations(primes, r):
            nrS = 1
            for p in S:
                nrS *= p
            ok(not Integer(nrS).is_square())        # prod P_p is not cO
    if ab is not None and D < 50:
        for p, P in Ps.items():
            x = find_norm(B, ab, P.rows(), [p, -p], 6) or find_norm(B, ab, P.rows(), [p, -p], 14)
            ok(x is not None, (D, p))
            ok(same(lattice([list(y * x) for y in basis]), P))       # P = O x
            ok(same(lattice([list(x * y) for y in basis]), P))       # P = x O
            xi = x**-1
            ok(same(lattice([list(x * y * xi) for y in basis]), Ol))  # x in N(O)
            ok(not Integer(abs(x.reduced_norm())).is_square())       # x not in QQ^* u(O)

# --- definite algebras: is P_D principal in each type? -------------------------
def has_norm(els, value):
    G = matrix(QQ, [[(x * y.conjugate()).reduced_trace() for y in els] for x in els])
    Qf = QuadraticForm(ZZ, G.change_ring(ZZ))
    return len(Qf.short_vector_list_up_to_length(value + 1)[value]) > 0


nonprincipal = []
for D in prime_range(200):
    Bm = BrandtModule(D)
    if D == 2:
        ok(Bm.dimension() == 1)                     # Remark (37.41)
        H = QuaternionAlgebra(QQ, -1, -1)
        i, j, k = H.gens()
        hur = [H(1), i, j, (1 + i + j + k) / 2]
        gram = matrix(QQ, [[(x * y).reduced_trace() for y in hur] for x in hur])
        ok(abs(gram.det()) == 4)                    # the order of Section 26 is maximal
        ok(H.discriminant() == 2)
    for I in Bm.right_ideals():
        Oi = I.left_order()
        bas = list(Oi.basis())
        P = two_sided_prime(bas, D)
        ok(abs(lattice([list(x) for x in bas]).solve_left(P).det()) == D**2)
        # an element of reduced norm D lies in P (O_i / P is a field) and
        # generates it (same index); so P is principal iff one exists
        principal = has_norm(bas, D)
        if not principal:
            nonprincipal.append(D)
ok(len(nonprincipal) > 0)

# --- (37.40)(ii): outer automorphisms of M_2(R) ---------------------------------
for dK, gen in [(-5, None), (-14, None)]:
    K = QuadraticField(dK, 's')
    s = K.gen()
    R = K.maximal_order()
    Cl = K.class_group()
    # an ideal of order exactly 2 in Cl
    a = None
    for p in prime_range(50):
        for P in K.primes_above(p):
            c = Cl(P)
            if c.order() == 2:
                a = P
            elif c.order() == 4:
                a = P**2
            if a is not None:
                break
        if a is not None:
            break
    ok(a is not None and not a.is_principal() and (a**2).is_principal())
    cgen = (a**2).gens_reduced()[0]
    ab = a.basis()
    x = None
    for cs in itertools.product(range(-2, 3), repeat=8):
        v1 = [cs[0] * ab[0] + cs[1] * ab[1], cs[2] * ab[0] + cs[3] * ab[1]]
        v2 = [cs[4] * ab[0] + cs[5] * ab[1], cs[6] * ab[0] + cs[7] * ab[1]]
        dt = v1[0] * v2[1] - v1[1] * v2[0]
        if dt != 0 and K.ideal(dt) == a**2:
            x = matrix(K, [v1, v2])
            break
    ok(x is not None, dK)
    # R^2 x = a + a: rows in a + a and determinant ideal a^2
    for i in range(2):
        for j in range(2):
            ok(K.ideal(x[i, j]) + a == a)
    ok(K.ideal(x.det()) == a**2)
    xi = x.inverse()

    def integral(m):
        return all(c.is_integral() for c in m.list())
    Rb = [K(1), K(R.basis()[1])]
    gensM = [matrix(K, 2, 2, {(i, j): r}) for i in range(2) for j in range(2) for r in Rb]
    ok(all(integral(xi * g * x) for g in gensM))   # x^-1 M_2(R) x in M_2(R)
    ok(all(integral(x * g * xi) for g in gensM))   # and conversely
    # not inner: x = lambda y would give (det x) = (lambda)^2, so a = (lambda)
    ok(not a.is_principal())
    y2 = x * x / cgen
    ok(integral(y2) and K(y2.det()).is_unit())     # i_x^2 is inner

# --- Exercises 38.3, 38.5 over ZZ ---------------------------------------------
E = [matrix(QQ, 2, 2, {(i, j): 1}) for i in range(2) for j in range(2)]
count = 0
for entries in itertools.product(range(-5, 6), repeat=4):
    x = matrix(QQ, 2, 2, list(entries))
    if x.det() == 0:
        continue
    xi = x.inverse()
    if all(all(c in ZZ for c in (x * e * xi).list()) for e in E):
        count += 1
        ok(all(all(c in ZZ for c in (xi * e * x).list()) for e in E))  # equality
        g = gcd(list(entries))
        ok(abs((x / g).det()) == 1)                                      # in QQ^* GL_2(ZZ)
ok(count > 0)

print(f'ok s37_picard: {N} checks')
