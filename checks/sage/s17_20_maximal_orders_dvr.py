"""Exact checks of Chapter 5, sections 17-20 (maximal orders over discrete
valuation rings), pp. 170-186, on quaternion algebras over Q.

  * For every quaternion algebra A over Q of discriminant D < 200 (all
    squarefree D > 1; definite or indefinite; Sage's maximal order Lambda)
    and for M_2(Z) (D = 1):
    - (20.3), (20.4), with (14.9): d(Lambda / Z) = D^2 up to sign, i.e. the
      local discriminant is p^(m(m-1) f) = p^2 at the ramified primes
      (index m = 2, f = 2) and 1 elsewhere (m = 1);
    - the inverse different Lambda~ (dual lattice under the reduced trace
      form) contains Lambda with index D^2; the different
      D(Lambda) = {x : x Lambda~ in Lambda} is a two-sided ideal with
      N(D) = card Lambda / D = D^2 = d(Lambda) (20.4) and D^2 = D Lambda,
      i.e. D_p = P_p = rad Lambda_p and P_p^2 = p Lambda_p (20.3), (19.3);
    - (17.5), (18.3): for each ramified p, P_p = D + p Lambda has
      index p^2, P_p^2 is in p Lambda, and Lambda / P_p = F_p[b] is a field
      with p^2 elements (the reduced char. pol. of b is irreducible mod p); for each unramified p < 20, the reduced trace form is
      nondegenerate mod p and Lambda / p Lambda is not commutative, so
      Lambda / p Lambda = M_2(F_p) and rad Lambda_p = p Lambda_p.
  * Remark (18.8)(iii) (with the correction Lambda -> Delta): for the
    Hurwitz order Delta in the skewfield (-1, -1)_Q and p = 3, Delta / 3 Delta
    has the zero divisor 1 + i + j (nr = 3), so it is not a skewfield.
  * (20.2): for Lambda = M_2(Delta), Delta the Hurwitz order, the dual of
    Lambda under the reduced trace of M_2(D) is M_2(Delta~).
  * (17.3)(ii), (18.7)(iii): [[Z, p^(-1) Z], [pZ, Z]] = u M_2(Z) u^(-1),
    u = diag(1, p), and has discriminant +-1 (p = 2, 3, 5).
  * (17.8)(ii): for Lambda = M_2(Delta), x_1 = diag(pi_D, 1), pi_D = 1 + i,
    card Lambda / x_1 Lambda = 16 = card of the simple module F_4^2 of
    Lambda / rad Lambda = M_2(F_4).
  * Exercises 19.1, 19.2: in M_2(Z), x_1 = diag(1, p), x_2 = diag(p, 1):
    p Lambda = Lambda x_1 . x_1^(-1) (Lambda x_2) x_1
             = Lambda x_2 . x_2^(-1) (Lambda x_1) x_2,
    two different proper factorizations (19.6), (19.7) of rad Lambda_p
    = p Lambda_p into t = 2 maximal integral ideals; M_1 M_2 and M_2 M_1
    have different left orders, so the factors do not commute.
  * (19.3): for the Hurwitz order at 2, P = (1 + i) Delta satisfies
    P^2 = 2 Delta and P P^(-1) = Delta with P^(-1) = 2^(-1) P.
What is NOT established: the general theorems; the local statements are
checked on Z-orders at the indicated primes.
"""
from itertools import product

from sage.all import (GF, QQ, ZZ, QuaternionAlgebra, identity_matrix, matrix,
                      prime_range, vector)

N = 0


def check(condition, label):
    global N
    assert condition, label
    N += 1


def lat(vectors):
    return matrix(QQ, [list(v) for v in vectors]).row_module(ZZ)


def gram(basis, tr):
    return matrix(QQ, len(basis), len(basis),
                  lambda a, b: tr(basis[a] * basis[b]))


def dual(basis, tr):
    G = gram(basis, tr)
    B = matrix(QQ, [list(b) for b in basis])
    return G.inverse() * B


def squarefree(n):
    return all(n % (p * p) != 0 for p in prime_range(2, 15))


Ds = [D for D in range(2, 200) if squarefree(D)]
for D in Ds:
    A = QuaternionAlgebra(D)
    check(A.discriminant() == D, 'discriminant of A')
    O = A.maximal_order()
    Ob = list(O.basis())
    tr = lambda z: z.reduced_trace()
    G = gram(Ob, tr)
    check(abs(G.det()) == D**2, '(20.4) d(Lambda) = D^2')
    Ol = lat(Ob)
    Dual_rows = dual(Ob, tr)
    Dl = Dual_rows.row_module(ZZ)
    check(Ol.is_submodule(Dl) and Ol.index_in(Dl) == D**2,
          '(20.1) inverse different, index D^2')
    dual_elems = [A(list(r)) for r in Dual_rows.rows()]
    # different: {x : x Lambda~ in Lambda}; it contains D Lambda; compute as
    # the dual of the Z-span of the conditions
    conds = []
    Omat_inv = matrix(QQ, [list(b) for b in Ob]).inverse()
    for y in dual_elems:
        for c in range(4):
            row = [(vector(QQ, list(e * y)) * Omat_inv)[c]
                   for e in [A(1), A.gen(0), A.gen(1), A.gen(2)]]
            conds.append(row)
    Bc = matrix(QQ, conds).row_module(ZZ).basis_matrix()
    Dif_std = Bc.inverse().transpose()        # in the standard basis 1,i,j,k
    Dif = [A(list(r)) for r in Dif_std.rows()]
    Difl = lat(Dif)
    check(Difl.is_submodule(Ol) and Difl.index_in(Ol) == D**2,
          '(20.4) N(D(Lambda)) = d(Lambda)')
    check(all(vector(QQ, list(a * x)) in Difl and vector(QQ, list(x * a))
              in Difl for a in Ob for x in Dif), 'different two-sided')
    D2 = lat([x * y for x in Dif for y in Dif])
    check(D2 == lat([D * b for b in Ob]), '(20.3) D^2 = D Lambda')
    for p in ZZ(D).prime_factors():
        Pp = lat(Dif + [p * b for b in Ob])
        check(Pp.index_in(Ol) == p**2, '(17.5) card Lambda/P = p^2')
        PP = lat([x * y for x in Dif + [p * b for b in Ob]
                  for y in Dif + [p * b for b in Ob]])
        check(PP.is_submodule(lat([p * b for b in Ob])),
              '(17.5) P^2 in p Lambda')
        # Lambda/P = F_p[b] for some b in Lambda, and b satisfies its reduced
        # characteristic polynomial: Lambda/P is a field of order p^2 iff
        # this polynomial is irreducible mod p.
        bs = [b for b in Ob
              if lat(Dif + [p * c for c in Ob] + [A(1), b]) == Ol]
        check(bs != [], 'Lambda = Z + Z b + P')
        b = bs[0]
        cp = b.reduced_characteristic_polynomial().change_ring(GF(p))
        check(cp.is_irreducible(), '(17.5), (18.7)(iv) Lambda/P = F_(p^2)')
    for p in prime_range(20):
        if D % p == 0:
            continue
        check(G.det() % p != 0, 'unramified p: trace form nondegenerate mod p')
        check(any(vector(QQ, list(a * b - b * a)) not in lat([p * c for c in Ob])
                  for a in Ob for b in Ob), 'Lambda/p Lambda = M_2(F_p)')

# M_2(Z): D = 1
Ms = [matrix(QQ, 2, 2, {(i, j): 1}) for i in range(2) for j in range(2)]
Gm = matrix(QQ, 4, 4, lambda a, b: (Ms[a] * Ms[b]).trace())
check(abs(Gm.det()) == 1, '(20.3) m = 1: different = Lambda')

# Remark (18.8)(iii)
H = QuaternionAlgebra(QQ, -1, -1)
qi, qj, qk = H.gens()
Hur = [(1 + qi + qj + qk) / 2, qi, qj, qk]
z = 1 + qi + qj
check(z.reduced_norm() == 3, 'nr(1 + i + j) = 3')
three = lat([3 * b for b in Hur])
check(vector(QQ, list(z)) not in three and vector(QQ, list(z * z.conjugate()))
      in three, 'Delta/3 Delta has zero divisors')

# (20.2) for M_2(Hurwitz)
trD = lambda w: w.reduced_trace()
Hdual = [H(list(r)) for r in dual(Hur, trD).rows()]


def m2(entries):
    return [[entries[0], entries[1]], [entries[2], entries[3]]]


def m2mul(x, y):
    return [[x[i][0] * y[0][j] + x[i][1] * y[1][j] for j in range(2)]
            for i in range(2)]


def m2tr(x):
    return x[0][0].reduced_trace() + x[1][1].reduced_trace()


def flat(x):
    return [c for row in x for e in row for c in list(e)]


zero = H(0)
LamM = []
for pos in range(4):
    for h in Hur:
        ent = [zero] * 4
        ent[pos] = h
        LamM.append(m2(ent))
DualM = []
for pos in range(4):
    for h in Hdual:
        ent = [zero] * 4
        ent[pos] = h
        DualM.append(m2(ent))
G16 = matrix(QQ, 16, 16, lambda a, b: m2tr(m2mul(LamM[a], LamM[b])))
Bm = matrix(QQ, [flat(x) for x in LamM])
dual16 = (G16.inverse() * Bm).row_module(ZZ)
check(dual16 == matrix(QQ, [flat(x) for x in DualM]).row_module(ZZ),
      '(20.2) Lambda~ = M_2(Delta~)')

# (17.3)(ii), (18.7)(iii)
for p in [2, 3, 5]:
    u = matrix(QQ, [[1, 0], [0, p]])
    conj = [u * m * u.inverse() for m in Ms]
    target = [Ms[0], Ms[1] / p, p * Ms[2], Ms[3]]
    check(lat([m.list() for m in conj]) == lat([m.list() for m in target]),
          '(17.3)(ii) conjugate maximal order')
    Gt = matrix(QQ, 4, 4, lambda a, b: (target[a] * target[b]).trace())
    check(abs(Gt.det()) == 1, 'conjugate order has discriminant +-1')

# (17.8)(ii)
piD = 1 + qi
x1 = m2([piD, zero, zero, H(1)])
x1L = [m2mul(x1, y) for y in LamM]
idx = matrix(QQ, [flat(x) for x in x1L]).row_module(ZZ).index_in(
    matrix(QQ, [flat(x) for x in LamM]).row_module(ZZ))
check(idx == 16, '(17.8)(ii) card Lambda/x_1 Lambda = 16')

# Exercises 19.1, 19.2


def latm(ms):
    return matrix(QQ, [m.list() for m in ms]).row_module(ZZ)


def prodlat(L1, L2):
    return latm([a * b for a in L1 for b in L2])


def left_order(L):
    rows = []
    L = [matrix(QQ, 2, 2, list(v)) for v in latm(L).basis()]
    B = matrix(QQ, [m.list() for m in L])
    Binv = B.inverse()
    for m in L:
        for c in range(4):
            rows.append([(vector(QQ, (e * m).list()) * Binv)[c] for e in Ms])
    Bc = matrix(QQ, rows).row_module(ZZ).basis_matrix()
    return Bc.inverse().transpose().row_module(ZZ)


for p in [2, 3, 5]:
    xa = matrix(QQ, [[1, 0], [0, p]])
    xb = matrix(QQ, [[p, 0], [0, 1]])
    Lam = Ms
    M1 = [m * xa for m in Lam]
    M2 = [xa.inverse() * m * xb * xa for m in Lam]
    M1b = [m * xb for m in Lam]
    M2b = [xb.inverse() * m * xa * xb for m in Lam]
    pL = latm([p * m for m in Lam])
    check(prodlat(M1, M2) == pL and prodlat(M1b, M2b) == pL,
          'Exercise 19.2: two factorizations of p Lambda')
    check(latm(M1) != latm(M1b), 'Exercise 19.2: different factors')
    check(left_order(M2) == latm([xa.inverse() * m * xa for m in Lam]),
          '(19.2) O_l(M_2) = O_r(M_1) = x^(-1) Lambda x')
    check(left_order([a * b for a in M1 for b in M2]) == latm(Lam)
          and left_order([a * b for a in M2 for b in M1]) == left_order(M2)
          != latm(Lam), 'Exercise 19.1: O_l(M_1 M_2) != O_l(M_2 M_1)')

# (19.3) at 2 for the Hurwitz order
P = [piD * b for b in Hur]
P2 = lat([x * y for x in P for y in P])
check(P2 == lat([2 * b for b in Hur]), '(19.3) P^2 = 2 Delta')
Pinv = [x / 2 for x in P]
check(lat([x * y for x in P for y in Pinv]) == lat(Hur),
      '(19.3) P P^(-1) = Delta')

print(f'ok s17_20_maximal_orders_dvr: {N} checks')
