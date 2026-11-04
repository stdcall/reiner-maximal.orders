"""Exact checks of Sections 21-25: maximal orders, ideals, norms, different.

Run with `sage -python`. Lattices are Z-lattices in QQ^n (Hermite normal
form of a row basis); products, colon lattices, inverses, left and right
orders and trace duals are computed directly from these bases, so the only
Sage results used without a check are the multiplication of quaternions,
the maximal orders returned by `maximal_order()` (their discriminants are
then checked) and Hilbert symbols (for the ramified primes).

The rational quaternion algebra of discriminant D is ramified exactly at the
primes p | D; its maximal order Lambda has local index m_p = 2 and local
capacity kappa_p = 1 at p | D, and m_p = 1, kappa_p = 2 at p not dividing D.

Section 21.
* (21.1), th:global-left-right-orders-maximal (p. 188): O_l(M) maximal iff
  O_r(M) maximal, for random full lattices M and random left ideals in the
  algebras D in ALGEBRAS (maximality = discriminant D^2, by (25.5) and
  (25.12)); both outcomes occur.
* (21.6), th:global-maximal-orders-simple (p. 189): Hom_Delta(M, M) is a
  maximal order of M_2(D) for random full right Delta-lattices M of D^2
  (D = 2, 3, 6); discriminant d(Delta)^4 (Exercise 25.1a with n = 4).

Section 22.
* (22.3), (22.4), (22.15), Exercise 22.13 (pp. 190-195): exhaustive over all
  F_p-subspaces of Lambda/p Lambda for D in SMALL_D and p <= 7: one maximal
  two-sided ideal over p; Lambda/frak(P) is M_2(F_p) (dimension 4, no
  nonzero zero ideal) or the field F_(p^2); maximal left ideals over p:
  p + 1 or 1, each containing frak(P); sum e f = 4.
* (22.4), (22.6), (22.7), (22.11), (22.14)(iii) for every squarefree D < 200
  and p | D or p <= 7 (all p < 40 when D < 60): frak(P) two-sided,
  frak(P)^(m_p) = p Lambda with m_p the local index, frak(P) frak(P)^(-1) =
  Lambda, prime ideals commute.
* (22.6), (22.7): L L^(-1) = Lambda, L^(-1) L = O_r(L), (L^(-1))^(-1) = L,
  O_l(L^(-1)) = O_r(L), O_r(L^(-1)) = O_l(L) for random left ideals L.
* (22.18), (22.19)(ii), (22.24), (22.25): the inductive construction of the
  proof of (22.18), run on Lambda x with nr x = p q, p^2 q, in both orders of
  the primes; the factors are maximal integral ideals in a proper product.
* (22.20)-(22.22): for D = 37, 101 (two types of maximal orders), M_12 =
  Lambda_1 Lambda_2 is normal, phi_12 is independent of M_12 and maps the
  primes of Lambda_1 to those of Lambda_2; maximal integral ideals belong to
  frak(P)_1 and phi_12(frak(P)_1).
* Exercise 22.1 (p. 202) for p = 2, 3, with M_3(Z) in place of M_3(R): no
  maximal left ideal of Lambda_1 has right order y Lambda_1 y^(-1).
* Exercise 22.2 (one direction on all index-2 superlattices, the hint's
  identity M N = M Lambda_2 N), Exercise 22.3 (sums and intersections).
* (22.14) with center L != K: M_2(Z[i]) at 2, e = 2, m = 1, sum e f = 8.

Section 23.
* (23.2) for random full lattices with arbitrary (non-maximal) orders;
  (23.3), (23.9): M^(-1) > Lambda for proper two-sided and left ideals;
  (23.9) the idempotent construction N L = frak(P) for p = 2, 3, 5.

Section 24.
* (24.2)(ii), (24.3), (24.4), (24.5), the norm of similar ideals, (24.9),
  (24.11), (24.12) (as the content of the norm form), (24.13), (24.14),
  Exercises 24.2, 24.3 and 24.5 ((i) <=> (iv)), on random ideals.
* (24.8): f and kappa from the enumeration above give N(M) = P^(f/kappa).
* (24.10): N_(K/Q) N_(L/K) = N_(L/Q) for ideals of L = Q(sqrt 2, i).

Section 25.
* (25.1), (25.2), (25.11), (25.12) for every squarefree D < 200:
  d(Lambda) = D^2 Z, N(frak(D)) = d, frak(D) = product of the frak(P),
  nr frak(D) = D; (25.3) for all types of maximal orders, D prime < 120.
* (25.12) with kappa_p = 2: Lambda = M_2(Delta), D = 2, 6: d = (nr frak D)^4
  with nr frak(D) = prod p^2.
* (25.4) for number fields: P^(e-1) | different, and P does not divide it
  if e = 1 (finite residue fields).
* Exercise 25.1a: d(M_2(O_L)/Z) = d_L^4; Exercise 25.3; Exercises 25.4,
  25.5 on the Hurwitz and Lipschitz orders.

Not covered: the proofs of the general theorems; Section 23 is checked only
through the statements it reproves; (21.2)-(21.5), (21.7), (22.23),
(24.1) beyond the examples, (25.4) for inseparable residue fields.
"""
from sage.all import (QQ, ZZ, GF, Integer, QuadraticField, QuaternionAlgebra,
                      block_matrix, factor, gcd, identity_matrix,
                      is_prime, matrix, prime_range, set_random_seed, vector)
import itertools
import random

set_random_seed(2175)
random.seed(2175)
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

# --- Section 21 ----------------------------------------------------------

maximal_seen = nonmaximal_seen = 0
for D in ALGEBRAS:
    B, A, Lam, nr = setup(D)
    dmax = disc(A, Lam)
    ok(dmax.abs() == D ** 2, '(25.12): d(Lambda) = D^2 for the maximal order')
    for trial in range(24):
        if trial % 2 == 0:  # a left ideal: its left order contains Lambda
            M = left_ideal(A, Lam, [rand_elt(Lam), rand_elt(Lam)])
        else:              # an arbitrary full lattice
            M = hnf([rand_elt(Lam, 2) for _ in range(4)]
                    + [7 * r for r in Lam.rows()])
        Ol, Or = O_l(A, M), O_r(A, M)
        left_max = disc(A, Ol) == dmax
        right_max = disc(A, Or) == dmax
        ok(left_max == right_max, '(21.1): O_l(M) maximal iff O_r(M) maximal')
        maximal_seen += left_max
        nonmaximal_seen += not left_max
ok(maximal_seen > 0 and nonmaximal_seen > 0, '(21.1): both cases occur')


class MatrixAlg2:
    """M_2(B) acting on columns B^2; elements as 16 and 8 coordinates."""

    def __init__(self, B):
        self.B = B
        q = lambda v: B(list(v))
        self.q = q

        def split(u, k):
            return [q(u[4 * i:4 * i + 4]) for i in range(k)]

        def join(xs):
            return vector(QQ, sum([list(x.coefficient_tuple()) for x in xs], []))

        def mul(u, v):
            a, b, c, d = split(u, 4)
            e, f, g, h = split(v, 4)
            return join([a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h])

        def act(u, w):
            a, b, c, d = split(u, 4)
            x, y = split(w, 2)
            return join([a * x + b * y, c * x + d * y])

        def trd(u):
            return 2 * (u[0] + u[12])
        self.alg = Alg(16, mul, trd)
        self.act, self.join, self.split = act, join, split


for D in [2, 3, 6]:
    B, A, Delta, nr = setup(D)
    MA = MatrixAlg2(B)
    dDelta = disc(A, Delta)
    for trial in range(3):
        # a random full right Delta-lattice in D^2: columns (x, y) with
        # x, y in Delta, transformed by a random invertible matrix
        while True:
            g = [B(list(rand_elt(Delta, 2))) for _ in range(4)]
            # invertible: g_3 != 0 and the Schur complement is nonzero
            if g[3] != 0 and g[0] - g[1] * g[3] ** -1 * g[2] != 0:
                break
        cols = []
        for d in Delta.rows():
            dq = B(list(d))
            cols.append(MA.join([g[0] * dq, g[2] * dq]))
            cols.append(MA.join([g[1] * dq, g[3] * dq]))
        M = hnf(cols)
        E16 = identity_matrix(QQ, 16).rows()
        maps = [matrix(QQ, [MA.act(e, m) for e in E16]) for m in M.rows()]
        End = transporter(maps, M)
        ok(disc(MA.alg, End) == dDelta ** 4,
           '(21.6): Hom_Delta(M, M) has the discriminant of M_2(Delta)')
        ok(O_l(MA.alg, End) == End, '(21.6): Hom_Delta(M, M) is an order')

# --- Section 22: exhaustive enumeration in Lambda / p Lambda --------------
# Linear algebra mod p is done on integer tuples (no matrices over GF(p)).

def span_set(rows, p, n=4):
    vecs = {tuple([0] * n)}
    for r in rows:
        vecs = {tuple((v[i] + c * r[i]) % p for i in range(n))
                for v in vecs for c in range(p)}
    return frozenset(vecs)


def subspaces(p, n=4):
    """All subspaces of F_p^n, from the reduced row echelon forms."""
    seen = set()
    for k in range(n + 1):
        for pivots in itertools.combinations(range(n), k):
            free = [(r, c) for r in range(k) for c in range(n)
                    if c > pivots[r] and c not in pivots]
            for vals in itertools.product(range(p), repeat=len(free)):
                rows = [[0] * n for _ in range(k)]
                for r in range(k):
                    rows[r][pivots[r]] = 1
                for (r, c), v in zip(free, vals):
                    rows[r][c] = v
                W = span_set(rows, p, n)
                assert W not in seen
                seen.add(W)
                yield k, rows, W


FK = {}
for D in SMALL_D:
    B, A, Lam, nr = setup(D)
    Linv = Lam.inverse()
    # structure constants: b_i b_j = sum_k c_ijk b_k, integral
    struct = [[A.mul(a, b) * Linv for b in Lam.rows()] for a in Lam.rows()]
    ok(all(c in ZZ for row in struct for v in row for c in v), 'Lambda is a ring')
    for p in [2, 3, 5, 7]:
        def mulp(x, y):
            return tuple(int(sum(x[i] * y[j] * struct[i][j][k]
                                 for i in range(4) for j in range(4))) % p
                         for k in range(4))
        left, two, count = [], [], 0
        for k, rows, W in subspaces(p):
            count += 1
            if k == 4:
                continue  # only proper ideals
            if all(mulp(e, w) in W for w in rows for e in identity_matrix(ZZ, 4).rows()):
                left.append((k, W))
                if all(mulp(w, e) in W for w in rows for e in identity_matrix(ZZ, 4).rows()):
                    two.append((k, W))
        maxtwo = [(k, W) for k, W in two if not any(W < U for _, U in two)]
        ok(len(maxtwo) == 1, '(22.4): one prime ideal of Lambda over p')
        ram = D % p == 0
        kP, P = maxtwo[0]
        f = 4 - kP
        maxleft = [(k, W) for k, W in left if not any(W < U for _, U in left)]
        ok(all(k == 2 for k, _ in maxleft), '(24.13): maximal left ideals have index p^2')
        if ram:
            ok(f == 2, '(22.14)(iii): Lambda/frak(P) = F_(p^2) at p | D')
            # coset representatives of Lambda/frak(P): a complement of P
            comp = [e for e in identity_matrix(ZZ, 4).rows()]
            basisP = []
            reps = None
            for c1, c2 in itertools.combinations(range(4), 2):
                S = span_set([comp[c1], comp[c2]], p)
                if len(S & P) == 1:
                    reps = S
                    break
            nonzero = [x for x in reps if any(x)]
            ok(all(mulp(x, y) not in P for x in nonzero for y in nonzero),
               '(22.3): Lambda/frak(P) has no zero divisors (a field) at p | D')
            ok(len(maxleft) == 1 and maxleft[0][1] == P,
               '(22.15): frak(P) is the only maximal left ideal over p | D')
            kappa = 1
        else:
            ok(kP == 0, '(22.4): frak(P) = p Lambda, Lambda/p Lambda simple')
            ok(len(maxleft) == p + 1, '(22.15): p + 1 maximal left ideals over p')
            kappa = 2
        ok(all(P <= W for _, W in maxleft), '(22.15): each M contains frak(P)')
        e = 2 if ram else 1
        ok(e * f == 4, 'Exercise 22.13: sum e_i f_i = (A : K)')
        ok(f % kappa == 0 and f // kappa == 2,
           '(24.8), (24.13): N(M) = P^(f/kappa) = P^n, n = 2')
        FK[(D, p)] = (f, kappa)

# --- Section 22: prime ideals for all squarefree D < 200 -----------------

for D in [d for d in range(1, 200) if squarefree(d)]:
    B, A, Lam, nr = setup(D)
    ram = ramified_primes(D)
    ok(sorted(B.ramified_primes()) == ram, 'discriminant of QuaternionAlgebra(D)')
    primes_here = sorted(set(ram + [p for p in prime_range(40)][:4]))
    if D < 60:
        primes_here = sorted(set(ram + list(prime_range(40))))
    Ps = {}
    for p in primes_here:
        Pp = prime_ideal(A, Lam, nr, p, p in ram)
        Ps[p] = Pp
        m = 2 if p in ram else 1
        ok(two_sided(A, Lam, Pp), '(22.4): frak(P) is a two-sided Lambda-ideal')
        ok(index(Lam, Pp) == p ** (4 // m), 'N(frak(P)) = P^f, f = 4/m')
        Pm = Pp if m == 1 else prod(A, Pp, Pp)
        ok(Pm == p * Lam, '(22.14)(iii), (25.11): P Lambda = frak(P)^(m_P)')
        ok(prod(A, Pp, inverse(A, Pp)) == Lam, '(22.6): frak(P) frak(P)^(-1) = Lambda')
    for p, q in itertools.combinations(sorted(Ps), 2):
        if D < 60 or (p in ram and q in ram):
            ok(prod(A, Ps[p], Ps[q]) == prod(A, Ps[q], Ps[p]),
               '(22.11): prime ideals commute')

for D in ALGEBRAS:
    B, A, Lam, nr = setup(D)
    for trial in range(6):
        L = left_ideal(A, Lam, [rand_elt(Lam), rand_elt(Lam)])
        Li = inverse(A, L)
        ok(prod(A, L, Li) == Lam, '(22.6): L L^(-1) = Lambda')
        ok(prod(A, Li, L) == O_r(A, L), '(22.6): L^(-1) L = O_r(L)')
        ok(inverse(A, Li) == L, '(22.6): (L^(-1))^(-1) = L')
        ok(O_l(A, Li) == O_r(A, L) and O_r(A, Li) == O_l(A, L), '(22.7)')
        if L != Lam:
            ok(contains(Li, Lam) and Li != Lam, '(23.9): L^(-1) > Lambda')


# --- (22.18), (22.19), (22.24), (22.25): factorization ---------------------

def maximal_left_containing(A, O, nrf, M, p):
    """A maximal left ideal N of O with M subset N, belonging to p."""
    N = hnf(M.rows() + [p * r for r in O.rows()])
    if index(O, N) == p ** 2:
        return N
    for c in itertools.product(range(-2, 3), repeat=4):
        y = vector(QQ, c) * O
        if nrf(y) % p == 0 and not contains(p * O, matrix(QQ, [y])):
            N = left_ideal(A, O, [y] + [p * r for r in O.rows()])
            if contains(N, M) and index(O, N) == p ** 2:
                return N
    raise ValueError('no maximal left ideal found')


def factorize(A, Lam, nrf, M, order_of_primes):
    factors, O, rest = [], Lam, M
    for p in order_of_primes:
        N = maximal_left_containing(A, O, nrf, rest, p)
        ok(O_l(A, N) == O and index(O, N) == p ** 2,
           '(22.18): the chosen factor is a maximal integral ideal')
        Ninv = inverse(A, N)
        newrest = prod(A, Ninv, rest)
        ok(prod(A, N, newrest) == rest, '(22.19)(ii): M = N (N^(-1) M)')
        Onew = O_r(A, N)
        ok(O_l(A, newrest) == Onew and contains(Onew, newrest),
           '(22.18): N^(-1) M is an integral left ideal of O_r(N)')
        factors.append(N)
        O, rest = Onew, newrest
    ok(rest == O, '(22.18): the factorization ends with the order')
    return factors


for D in [2, 6, 13, 37]:
    B, A, Lam, nr = setup(D)
    targets = []
    for c in itertools.product(range(-3, 4), repeat=4):
        x = vector(QQ, c) * Lam
        n = nr(x)
        if n > 1 and len(factor(n)) == 2 and sum(e for _, e in factor(n)) <= 3:
            targets.append((x, n))
        if len(targets) >= 4:
            break
    ok(len(targets) == 4, '(22.18): test elements found')
    for x, n in targets:
        M = left_ideal(A, Lam, [x])
        ok(index(Lam, M) == n ** 2, '(24.2)(ii), Exercise 26.3: [Lambda : Lambda x] = nr(x)^2')
        primes_mult = sum([[p] * e for p, e in factor(n)], [])
        for order in set(itertools.permutations(primes_mult)):
            fs = factorize(A, Lam, nr, M, order)
            ok(len(fs) == len(primes_mult), '(22.24): number of factors')
            P = fs[0]
            for N in fs[1:]:
                P = prod(A, P, N)
            ok(P == M, '(22.18): M is the proper product of the factors')
            ok(all(O_r(A, fs[i]) == O_l(A, fs[i + 1]) for i in range(len(fs) - 1)),
               '(22.18): the product is proper')
            ok(O_r(A, fs[-1]) == O_r(A, M), '(22.18): O_r(M) = O_r(M_k)')
            ok([(index(O_l(A, N), N)).sqrt() for N in fs] == list(order),
               '(22.25): composition factors in the preassigned order')
            nrs = [gcd([nr(r) for r in N.rows()] +
                       [nr(r + s) for r in N.rows() for s in N.rows()]) for N in fs]
            ok(nrs == list(order), '(24.13): nr M_i = P_i')

# --- (22.20)-(22.22) with two types of maximal orders -------------------------

from sage.all import BrandtModule
for p in [37, 101]:
    I = BrandtModule(p).right_ideals()
    B = I[0].quaternion_algebra()
    A = quaternion_alg(B)
    nr = lambda v, B=B: B(list(v)).reduced_norm()
    orders = []
    for J in I:
        Ol = hnf([vector(QQ, b.coefficient_tuple()) for b in J.left_order().basis()])
        if all(Ol != O for O in orders):
            orders.append(Ol)
    ok(len(orders) >= 2, 'two types of maximal orders')
    L1, L2 = orders[0], orders[1]
    M12 = prod(A, L1, L2)
    ok(O_l(A, M12) == L1 and O_r(A, M12) == L2, '(22.20): Lambda_1 Lambda_2 is M_12')
    x = rand_elt(L1)
    N12 = prod(A, prod(A, L1, matrix(QQ, [x])), L2)
    ok(O_l(A, N12) == L1 and O_r(A, N12) == L2, '(22.20): another M_12')
    for q in [2, 3, p]:
        P1 = prime_ideal(A, L1, nr, q, q == p)
        P2 = prime_ideal(A, L2, nr, q, q == p)
        phi = prod(A, prod(A, inverse(A, M12), P1), M12)
        phi2 = prod(A, prod(A, inverse(A, N12), P1), N12)
        ok(phi == P2 and phi2 == P2, '(22.20), (22.21): phi_12 maps primes to primes')
        ok(index(L1, P1) == index(L2, P2), '(24.7): similar primes have equal norms')
    # a maximal integral ideal M of Lambda_1 belonging to frak(P)_1, q = 2
    M = maximal_left_containing(A, L1, nr, 2 * L1, 2)
    L3 = O_r(A, M)
    P1 = prime_ideal(A, L1, nr, 2, False)
    P3 = prime_ideal(A, L3, nr, 2, False)
    phi = prod(A, prod(A, inverse(A, M), P1), M)
    ok(phi == P3 and contains(M, phi), '(22.22): M belongs to phi_12(frak(P)_1)')
    ok(contains(M, P1), '(22.15): M belongs to frak(P)_1')

# --- Exercise 22.1: M_3(Z), y = diag(1, 1, p) --------------------------------

def mat_alg(n):
    def mul(u, v):
        return vector(QQ, (matrix(QQ, n, n, list(u)) * matrix(QQ, n, n, list(v))).list())
    return Alg(n * n, mul, lambda u: matrix(QQ, n, n, list(u)).trace())


A3 = mat_alg(3)
L1 = identity_matrix(QQ, 9)
for p in [2, 3]:
    y = matrix(QQ, [[1, 0, 0], [0, 1, 0], [0, 0, p]])
    L2 = hnf([vector(QQ, (y * matrix(QQ, 3, 3, list(r)) * y.inverse()).list()) for r in L1.rows()])
    ok(O_l(A3, L2) == L2, 'Exercise 22.1: Lambda_2 is an order')
    count = 0
    # maximal left ideals of M_3(Z) over p: rows in a sublattice of index p
    for k, basis, _ in subspaces(p, 3):
        if k != 2:
            continue
        rows = [vector(ZZ, b) for b in basis] + \
            [p * vector(ZZ, e) for e in identity_matrix(ZZ, 3).rows()]
        X = matrix(QQ, rows).change_ring(ZZ).echelon_form()
        X = X.matrix_from_rows(range(3)).change_ring(QQ)
        M = left_ideal(A3, L1, [vector(QQ, X.list())])
        count += 1
        ok(index(L1, M) == p ** 3, 'Exercise 22.1: maximal left ideal of index p^3')
        ok(O_r(A3, M) != L2, 'Exercise 22.1: O_r(M) != y Lambda_1 y^(-1)')
        ok(X.change_ring(ZZ).elementary_divisors() == [1, 1, p],
           'Exercise 22.1 hint: x has elementary divisors {1, 1, p}')
    ok(count == p ** 2 + p + 1, 'Exercise 22.1: all maximal left ideals over p')

# --- Exercises 22.2, 22.3 ---------------------------------------------------

for D in [2, 6]:
    B, A, Lam, nr = setup(D)
    while True:  # a left ideal whose right order differs from Lambda
        Mx = left_ideal(A, Lam, [rand_elt(Lam), 5 * Lam.row(1)])
        if O_r(A, Mx) != Lam:
            break
    N = left_ideal(A, O_r(A, Mx), [rand_elt(O_r(A, Mx)), 7 * Lam.row(0)])
    MN = prod(A, Mx, N)
    for c in itertools.product(range(2), repeat=4):
        if any(c):
            bigger = hnf(Mx.rows() + [vector(QQ, c) * Mx / 2])
            ok(prod(A, bigger, N) != MN, 'Exercise 22.2: a proper product grows')
            bigger = hnf(N.rows() + [vector(QQ, c) * N / 2])
            ok(prod(A, Mx, bigger) != MN, 'Exercise 22.2: a proper product grows')
    # an improper product M N with O_r(M) != O_l(N): M Lambda_2 N = M N
    N2 = left_ideal(A, Lam, [rand_elt(Lam), 7 * Lam.row(0)])
    ok(O_r(A, Mx) != O_l(A, N2), 'Exercise 22.2: an improper product')
    if O_r(A, Mx) != O_l(A, N2):
        L2N = prod(A, O_r(A, Mx), N2)
        ok(L2N != N2 and prod(A, Mx, L2N) == prod(A, Mx, N2),
           'Exercise 22.2 hint: M N = M Lambda_2 N for an improper product')
    ram = ramified_primes(D)
    P = {p: prime_ideal(A, Lam, nr, p, True) for p in ram}

    def power(I, k):
        if k >= 0:
            R = Lam
            for _ in range(k):
                R = prod(A, R, I)
            return R
        return power(inverse(A, I), -k)

    def ideal(exps):
        R = Lam
        for p, k in zip(ram, exps):
            R = prod(A, R, power(P[p], k))
        return R
    box = list(itertools.product(range(-2, 3), repeat=len(ram)))
    for a in box:
        for b in box:
            Ia, Ib = ideal(a), ideal(b)
            ok(contains(Ia, Ib) == all(x <= y for x, y in zip(a, b)), 'Exercise 22.3(i)')
            ok(hnf(Ia.rows() + Ib.rows()) == ideal([min(x, y) for x, y in zip(a, b)]),
               'Exercise 22.3(ii)')
            inter = dual_cols(hnf(dual_cols(Ia.transpose()).rows() + dual_cols(Ib.transpose()).rows()).transpose())
            ok(inter == ideal([max(x, y) for x, y in zip(a, b)]), 'Exercise 22.3(iii)')

# --- (22.14) with center L = Q(i): Lambda = M_2(Z[i]) --------------------------

def m2_over_gaussian():
    K = QuadraticField(-1, 'i')
    i = K.gen()

    def to_mat(u):
        return matrix(K, 2, 2, [u[0] + u[1] * i, u[2] + u[3] * i, u[4] + u[5] * i, u[6] + u[7] * i])

    def from_mat(X):
        return vector(QQ, sum([list(X[r, s].list()) for r in range(2) for s in range(2)], []))

    def mul(u, v):
        return from_mat(to_mat(u) * to_mat(v))
    return Alg(8, mul, lambda u: to_mat(u).trace().trace())


A8 = m2_over_gaussian()
Lam8 = identity_matrix(QQ, 8)
ok(abs(disc(A8, Lam8)) == 4 ** 4, 'Exercise 25.1a: d(M_2(Z[i])/Z) = d_L^4 = 4^4')
pi8 = vector(QQ, [1, 1, 0, 0, 0, 0, 1, 1])  # (1 + i) times the identity matrix
P8 = left_ideal(A8, Lam8, [pi8])
ok(two_sided(A8, Lam8, P8) and prod(A8, P8, P8) == 2 * Lam8,
   '(22.14)(i): 2 Lambda = frak(P)^(e m), e = 2, m = 1')
ok(index(Lam8, P8) == 2 ** 4, 'Exercise 22.13: f = 4, e f = 8 = (A : Q)')

# --- Section 23 ---------------------------------------------------------------

for D in ALGEBRAS[:6]:
    B, A, Lam, nr = setup(D)
    for trial in range(10):
        M = hnf([rand_elt(Lam, 2) for _ in range(4)] + [5 * r for r in Lam.rows()])
        ok(contains(O_l(A, M), M) == contains(O_r(A, M), M),
           '(23.2): M subset O_l(M) iff M subset O_r(M), any orders')
    for p in ramified_primes(D):
        Pp = prime_ideal(A, Lam, nr, p, True)
        Pi = inverse(A, Pp)
        ok(contains(Pi, Lam) and Pi != Lam, '(23.3): frak(P)^(-1) > Lambda')

# (23.9): N = Lambda (1 - e) + frak(P), L = e Lambda + frak(P), N L = frak(P)
for D, p in [(1, 2), (3, 2), (2, 3), (6, 5), (13, 3)]:
    B, A, Lam, nr = setup(D)
    one = vector(QQ, [1, 0, 0, 0])
    found = 0
    for c in itertools.product(range(p), repeat=4):
        e = vector(QQ, c) * Lam
        e2 = A.mul(e, e)
        if not contains(p * Lam, matrix(QQ, [e2 - e])):
            continue
        if contains(p * Lam, matrix(QQ, [e])) or contains(p * Lam, matrix(QQ, [e - one])):
            continue
        N = left_ideal(A, Lam, [one - e] + [p * r for r in Lam.rows()])
        L = hnf([A.mul(e, l) for l in Lam.rows()] + [p * r for r in Lam.rows()])
        ok(index(Lam, N) == p ** 2, '(23.9): N is a maximal left ideal')
        ok(prod(A, N, L) == p * Lam, '(23.9): N L = frak(P) = p Lambda')
        found += 1
        if found >= 3:
            break
    ok(found >= 1, '(23.9): a primitive idempotent exists')

# --- Section 24 ---------------------------------------------------------------

for D in ALGEBRAS:
    B, A, Lam, nr = setup(D)
    for trial in range(6):
        a = rand_invertible(Lam, nr)
        La, aL = left_ideal(A, Lam, [a]), hnf([A.mul(a, l) for l in Lam.rows()])
        ok(index(Lam, La) == nr(a) ** 2, '(24.2)(ii): N(Lambda a) = R N(a)')
        ok(index(O_l(A, aL), aL) == nr(a) ** 2, '(24.2)(ii): N(a Lambda) = R N(a)')
        M = left_ideal(A, Lam, [rand_elt(Lam), rand_elt(Lam)])
        Or = O_r(A, M)
        ok(index(Lam, M) == index(Or, M), '(24.3): norm by left or right order')
        content = gcd([nr(r) for r in M.rows()] +
                      [nr(r + s) - nr(r) - nr(s) for r in M.rows() for s in M.rows()])
        ok(content ** 2 == index(Lam, M), '(24.9), (24.11), (24.12): nr M = content of nr on M')
        Mi = inverse(A, M)
        ok(index(Mi, Lam) == index(Lam, M), 'Exercise 24.2: ord M^(-1)/Lambda = ord Lambda/M')
        N = left_ideal(A, Or, [rand_elt(Or), rand_elt(Or)])
        MN = prod(A, M, N)
        ok(index(Lam, MN) == index(Lam, M) * index(Or, N), '(24.4): N(L M) = N(L) N(M)')
        # (24.5): N*(J) for a normal ideal J = M / alpha
        J = M / 6
        for alpha in [6, 12, 30]:
            ok(index(Lam, alpha * J) / QQ(alpha) ** 4 == index(Lam, M) / QQ(6) ** 4,
               '(24.5): N*(J) does not depend on alpha')
        alpha = index(Lam, M)
        ok(contains(Lam, alpha * Mi) and
           index(Lam, alpha * Mi) / QQ(alpha) ** 4 == 1 / index(Lam, M),
           '(24.5): N*(J^(-1)) = N*(J)^(-1)')
        # similar two-sided ideals: L^(-1) J L has the norm of J
        for p in ramified_primes(D)[:1]:
            Pp = prime_ideal(A, Lam, nr, p, True)
            S = prod(A, prod(A, Mi, Pp), M)
            ok(two_sided(A, Or, S) and index(Or, S) == index(Lam, Pp),
               '(24.5): similar ideals have the same norm')
        # Exercise 24.5, (i) <=> (iv), with J = p Lambda or frak(P)
        for p in [2, 3, 5]:
            Jp = prime_ideal(A, Lam, nr, p, D % p == 0)
            coprime = hnf(M.rows() + Jp.rows()) == Lam
            ok(coprime == (gcd(index(Lam, M), index(Lam, Jp)) == 1), 'Exercise 24.5')
    # (24.14): nr(Lambda x) = product of annihilators of composition factors
    for x in [rand_invertible(Lam, nr) for _ in range(4)]:
        n = nr(x)
        M = left_ideal(A, Lam, [x])
        ok(index(Lam, M) == n ** 2, '(24.14): N(M) = (prod P_i)^2')

# (24.10): transitivity of norms in Q < K = Q(sqrt 2) < L = K(i)
from sage.all import NumberField, PolynomialRing
K2 = QuadraticField(2, 's')
T = PolynomialRing(K2, 't').gen()
Lrel = K2.extension(T ** 2 + 1, 'i')
for gens in [(3, Lrel.gen() + 1), (5, Lrel.gen() + 2), (7, K2.gen() + Lrel.gen())]:
    J = Lrel.ideal(list(gens))
    ok(J.relative_norm().absolute_norm() == J.absolute_norm(), '(24.10)')

# --- Section 25 ---------------------------------------------------------------

for D in [d for d in range(1, 200) if squarefree(d)]:
    B, A, Lam, nr = setup(D)
    d = disc(A, Lam)
    ok(d.abs() == D ** 2, '(25.12): d(Lambda/Z) = (nr frak(D))^2, nr frak(D) = D')
    Lt = trace_dual(A, Lam)
    ok(two_sided(A, Lam, Lt) and contains(Lt, Lam), '(25.1): inverse different two-sided')
    Dif = inverse(A, Lt)
    ok(two_sided(A, Lam, Dif) and contains(Lam, Dif), 'frak(D) is a two-sided ideal')
    ok(index(Lam, Dif) == d.abs(), '(25.2): d = N(frak(D))')
    ok(index(Lt, Lam) == d.abs(), '(25.2) proof: ord tilde(Lambda)/Lambda = d')
    if D < 60:
        prodP = Lam
        for p in ramified_primes(D):
            prodP = prod(A, prodP, prime_ideal(A, Lam, nr, p, True))
        ok(prodP == Dif, '(25.11): frak(D) = product of frak(P)^(m_P - 1)')
        for p in ramified_primes(D) + [q for q in [2, 3, 5] if D % q]:
            Jp = prime_ideal(A, Lam, nr, p, D % p == 0)
            ok(trace_dual(A, Jp) == prod(A, Lt, inverse(A, Jp)),
               '(25.1): tilde(J) = tilde(Lambda) J^(-1)')
    ok(prod(A, Dif, Dif) == D * Lam, '(25.11): frak(D)^2 = D Lambda')
    content = gcd([nr(r) for r in Dif.rows()] +
                  [nr(r + s) - nr(r) - nr(s) for r in Dif.rows() for s in Dif.rows()])
    ok(content == D, '(25.12), (24.12): nr frak(D) = D')

# (25.3): the discriminant does not depend on the maximal order
for p in prime_range(120):
    I = BrandtModule(p).right_ideals()
    B = I[0].quaternion_algebra()
    A = quaternion_alg(B)
    ds = set()
    for J in I:
        Ol = hnf([vector(QQ, b.coefficient_tuple()) for b in J.left_order().basis()])
        ds.add(disc(A, Ol).abs())
    ok(ds == {p ** 2}, '(25.3): all maximal orders have discriminant p^2')

# (25.12) with kappa = 2: Lambda = M_2(Delta)
for D in [2, 6]:
    B, A, Delta, nr = setup(D)
    MA = MatrixAlg2(B)
    rows = []
    for k in range(4):
        for d in Delta.rows():
            u = [vector(QQ, 4)] * 4
            u[k] = d
            rows.append(vector(QQ, sum([list(x) for x in u], [])))
    L16 = hnf(rows)
    groundideal = 1
    for p in ramified_primes(D):
        groundideal *= p ** ((2 - 1) * 2)  # p^((m_P - 1) kappa_P)
    ok(abs(disc(MA.alg, L16)) == groundideal ** 4, '(25.12): d = (nr frak(D))^n, n = 4')
    ok(O_l(MA.alg, L16) == L16, 'M_2(Delta) is an order')

# (25.4) for number fields: P^(e-1) divides the different; P does not if e = 1
x = PolynomialRing(QQ, 'x').gen()
for poly in [x ** 2 - 2, x ** 2 + 1, x ** 2 + 3, x ** 3 - 2, x ** 4 + 1,
             x ** 4 + x ** 3 + x ** 2 + x + 1, x ** 3 - 3 * x + 1, x ** 5 - 2]:
    Lf = NumberField(poly, 'a')
    Dif = Lf.different()
    for p in prime_range(12):
        for P, e in Lf.ideal(p).factor():
            v = Dif.valuation(P)
            ok(v >= e - 1, '(25.4): frak(P)^(e-1) divides the different')
            if e == 1:
                ok(v == 0, '(25.4): e = 1 and finite residue field: P does not divide D')

# Exercise 25.1a with L = Q(sqrt 2); Exercise 25.1a for A = Q + Hurwitz
A8b = None
K = QuadraticField(2, 'r')
rr = K.gen()


def to_mat2(u):
    return matrix(K, 2, 2, [u[0] + u[1] * rr, u[2] + u[3] * rr, u[4] + u[5] * rr, u[6] + u[7] * rr])


A8b = Alg(8, lambda u, v: vector(QQ, sum([list((to_mat2(u) * to_mat2(v))[r, s].list())
                                          for r in range(2) for s in range(2)], [])),
          lambda u: to_mat2(u).trace().trace())
ok(abs(disc(A8b, identity_matrix(QQ, 8))) == 8 ** 4, 'Exercise 25.1a: d = d_L^4 = 8^4')
B, A, Lam, nr = setup(2)
A5 = Alg(5, lambda u, v: vector(QQ, [u[0] * v[0]] + list(A.mul(u[1:], v[1:]))),
         lambda u: u[0] + A.trd(u[1:]))
L5 = block_matrix(QQ, [[matrix(QQ, [[1]]), 0], [0, Lam]])
ok(disc(A5, L5) == 1 * disc(A, Lam), 'Exercise 25.1a: d(Lambda) = prod d(Lambda_i)')

# Exercise 25.3: complementary ideals of normal ideals M_12
for D in [2, 6, 37]:
    B, A, Lam, nr = setup(D)
    for trial in range(4):
        M = left_ideal(A, Lam, [rand_elt(Lam), rand_elt(Lam)])
        L2 = O_r(A, M)
        Mt = trace_dual(A, M)
        Mi = inverse(A, M)
        ok(Mt == prod(A, trace_dual(A, L2), Mi) == prod(A, Mi, trace_dual(A, Lam)),
           'Exercise 25.3: tilde(M) = tilde(Lambda_2) M^(-1) = M^(-1) tilde(Lambda_1)')
        ok(O_l(A, Mt) == L2 and O_r(A, Mt) == Lam, 'Exercise 25.3: tilde(M) = tilde(M)_21')
        ok(trace_dual(A, Mt) == M, 'Exercise 25.3: tilde(tilde(M)) = M')

# Exercises 25.4, 25.5: R-units of the Hurwitz order; Lipschitz units
B, A, Lam, nr = setup(2)
Lip = identity_matrix(QQ, 4)
for c in itertools.product(range(-2, 3), repeat=4):
    a = vector(QQ, c) * Lam
    if a.is_zero():
        continue
    ainv = vector(QQ, (B(list(a)) ** -1).coefficient_tuple())
    integral = B(list(ainv)).reduced_trace() in ZZ and B(list(ainv)).reduced_norm() in ZZ
    ok(integral == (nr(a) ** 2 == 1), 'Exercise 25.4: R-unit iff N(a) unit')
    inLip = contains(Lip, matrix(QQ, [a]))
    if inLip:
        ok(contains(Lip, matrix(QQ, [ainv])) == contains(Lam, matrix(QQ, [ainv])),
           'Exercise 25.5: u(Gamma) = Gamma n u(Gamma\')')

print('ok s21_25_ideal_theory: %d checks' % COUNT[0])
