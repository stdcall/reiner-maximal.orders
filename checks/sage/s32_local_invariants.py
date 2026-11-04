"""Local invariants and splitting of quaternion algebras over QQ (Section 32).

Checked, with exact arithmetic over QQ, number fields and finite fields:

* (32.2), (32.4), (32.13a), Exercise 32.1 (pp. 273-281): for every
  quaternion algebra (a, b)_QQ with a, b squarefree, a, b != 0, 1,
  |a|, |b| <= 30, the set of ramified places (Hilbert symbols at the real
  place and at the primes dividing 2ab) has even size, so the local
  invariants (1/2 at each ramified place, (32.4)) sum to 0 in QQ/ZZ; the
  algebra is either split or ramified at >= 2 places (Exercise 32.1); it
  ramifies at the real place iff a < 0 and b < 0 (A_R = H, (32.2)).
* Hasse-Brauer-Noether-Albert (32.11) (p. 276), constructively: whenever
  no place ramifies, the conic a x^2 + b y^2 = z^2 has an explicit rational
  point, so (a, b)_QQ is split.
* Example after (32.20) (p. 281) for A = (QQ(sqrt a)/QQ, sigma, b) = (a, b):
  at an odd prime p < 100 not dividing a, inv_p A = v_p(b)/n_p with n_p = 2
  if p is inert and 1 if p splits in QQ(sqrt a) (case (iii)); at the real
  place A_R = H iff a < 0 and b < 0, and A_R splits if a > 0 (cases (i),
  (ii)).
* (32.15) (p. 278): for (a, b) with |a|, |b| <= 10 and every quadratic field
  L = QQ(sqrt d), d squarefree, |d| <= 30: whenever d is not a local square
  at any ramified place (m_P = 2 divides (L_p : K_P)), an explicit pure
  quaternion x with x^2 = d is found, so L embeds in A as a maximal subfield
  and splits A; otherwise d is a square at some ramified place.
* Exercise 32.3 (pp. 281-282): N_{L_p/QQ_p}(f(x)) = N_{L/QQ}(x) with
  f(x) = prod sigma_i(x) over right cosets G_p sigma_i, for L the splitting
  field of X^3 - 2 (galois group S_3), p = 2, 3, 5, 7, 31 and four elements
  x, the local norm being the product over G_p (32.6); n_p = |G_p| = e f
  divides 6 (32.8).  For p = 5 (G_p not normal) a choice of left coset
  representatives sigma_i G_p makes the identity fail: a refuted variant.
* (32.1)(i)-(iv) (p. 273) for a maximal order O of the quaternion algebra of
  each squarefree discriminant 1 < D < 200 (definite for an odd number of
  prime factors, indefinite otherwise): for p | D the prime ideal P_p of O
  (the radical of O/pO, lifted) is two-sided with [O : P_p] = p^2,
  nr P_p = pZ and P_p^2 = pO (m_p = 2); for primes p < 30 not dividing D,
  O/pO is semisimple with 1-dimensional center, hence ~ M_2(F_p) (m_p = 1);
  the dual of O for the reduced trace equals (prod P_p)^{-1}, that is, the
  different is prod P_p^{m_p - 1}; the discriminant is
  D^2 = prod p^{(m_p - 1) kappa_p sqrt(A : K)}; for M_2(O) (kappa_p = 2,
  sqrt(A : K) = 4) it is D^8.

The radical of O/pO is computed by the characteristic-p algorithm of
Friedl-Ronyai, run with integer matrices (radical_mod_p).

Not established: the theorems over other global fields or in other
degrees; Grunwald-Wang (32.18); the surjectivity in (32.13) beyond these
algebras.
"""
from sage.all import (QQ, ZZ, GF, Integer, Conic, DiagonalQuadraticForm,
                      NumberField, PolynomialRing, QuaternionAlgebra,
                      gcd, hilbert_symbol, identity_matrix, kronecker_symbol,
                      matrix, prime_range, prod, vector)

N = 0


def ok(cond, msg=''):
    global N
    assert cond, msg
    N += 1


def squarefree_range(bound):
    vals = [d for d in range(-bound, bound + 1)
            if d not in (0, 1) and Integer(d).is_squarefree()]
    return vals


def ramified(a, b):
    places = [-1] + sorted(set(Integer(2 * a * b).prime_divisors()))
    return [v for v in places if hilbert_symbol(a, b, v) == -1]


def local_square(d, v):
    if v == -1:
        return d > 0
    return QQ(d).is_padic_square(v)


# --- (32.2), (32.4), (32.5a), Exercise 32.1, (32.6) -----------------------
vals = squarefree_range(30)
for a in vals:
    for b in vals:
        ram = ramified(a, b)
        ok(len(ram) % 2 == 0, (a, b))                 # sum of 1/2's is 0
        ok(len(ram) == 0 or len(ram) >= 2, (a, b))    # Exercise 32.1
        ok((-1 in ram) == (a < 0 and b < 0), (a, b))  # A_R = H iff a, b < 0
        if not ram:
            found, pt = Conic(QQ, [a, b, -1]).has_rational_point(point=True)
            ok(found)
            x, y, z = pt
            ok(a * x**2 + b * y**2 == z**2 and (x, y, z) != (0, 0, 0))

# --- Example after (32.13): invariants at unramified primes ---------------
for a in vals:
    for b in vals:
        ram = ramified(a, b)
        for p in prime_range(3, 100):
            if a % p == 0:
                continue
            n_p = 1 if kronecker_symbol(a, p) == 1 else 2
            inv = QQ(Integer(b).valuation(p)) / n_p
            ok((inv.denominator() == 2) == (p in ram), (a, b, p))
        # real place: P real, its extension to QQ(sqrt a) complex iff a < 0
        if a > 0:
            ok(-1 not in ram)
        else:
            ok((-1 in ram) == (b < 0))

# --- (32.8): quadratic splitting fields -----------------------------------
small = squarefree_range(10)
dvals = squarefree_range(30)
for a in small:
    for b in small:
        ram = ramified(a, b)
        Q = DiagonalQuadraticForm(QQ, [a, b, -a * b])   # x^2 for pure x
        for d in dvals:
            crit = all(not local_square(d, v) for v in ram)
            if crit:
                x = Q.solve(d)
                ok(Q(x) == d and x != 0, (a, b, d))
            else:
                ok(any(local_square(d, v) for v in ram))

# --- Exercise 32.3 ----------------------------------------------------------
R = PolynomialRing(QQ, 'X')
X = R.gen()
L = NumberField(X**3 - 2, 'c').galois_closure('w')
G = L.galois_group()
ok(G.order() == 6)
elements = list(G)
test_elements = [L.gen() + 1, L.gen()**2 - 3 * L.gen() + 2,
                 (L.gen()**4 + L.gen() - 5) / 3, 7 * L.gen()**5 + 1]
for p in [2, 3, 5, 7, 31]:
    P = L.primes_above(p)[0]
    Gp = G.decomposition_group(P)
    e, f = P.ramification_index(), P.residue_class_degree()
    ok(Gp.order() == e * f and 6 % Gp.order() == 0, p)
    Gp_list = list(Gp)
    right_reps, seen = [], set()
    for s in elements:
        coset = frozenset(r * s for r in Gp_list)
        if coset not in seen:
            seen.add(coset)
            right_reps.append(s)
    ok(len(right_reps) == 6 // Gp.order())
    for x in test_elements:
        fx = prod(s(x) for s in right_reps)
        local = prod(r(fx) for r in Gp_list)
        ok(local == x.norm(), (p, x))
    if p == 5:
        # Left cosets s G_p: with these representatives rho s misses part of
        # G, and the identity fails (refuted variant).
        Gp_set = set(Gp_list)
        missed = False
        for s1 in elements:
            for s2 in elements:
                for s3 in elements:
                    reps = [s1, s2, s3]
                    cosets = {frozenset(t * r for r in Gp_list) for t in reps}
                    if len(cosets) != 3:
                        continue
                    if len({r * t for r in Gp_list for t in reps}) == 6:
                        continue
                    x = test_elements[1]
                    fx = prod(t(x) for t in reps)
                    ok(prod(r(fx) for r in Gp_list) != x.norm())
                    missed = True
                    break
                if missed:
                    break
            if missed:
                break
        ok(missed and not Gp.is_normal(G))


# --- (32.1) and the different for maximal quaternion orders ----------------
def algebra_with_discriminant(D):
    primes = Integer(D).prime_divisors()
    if len(primes) % 2 == 1:
        return QuaternionAlgebra(D)
    for a in [-1, -2, -3, -5, -6, -7, -10, -11, -13, -14, -15, 2, 3, 5]:
        for b in list(range(-200, 0)) + list(range(2, 200)):
            if not Integer(b).is_squarefree():
                continue
            if sorted(v for v in ramified(a, b) if v != -1) == primes \
                    and -1 not in ramified(a, b):
                return QuaternionAlgebra(QQ, a, b)
    raise ValueError(D)


def lattice(rows):
    """HNF basis of the ZZ-span of rational row vectors."""
    M = matrix(QQ, rows)
    den = M.denominator()
    H = (den * M).change_ring(ZZ).echelon_form(include_zero_rows=False)
    return H.change_ring(QQ) / den


def contains(big, small):
    return all(big.solve_left(v).denominator() == 1 for v in small.rows())


def same(L1, L2):
    return L1.nrows() == L2.nrows() and contains(L1, L2) and contains(L2, L1)


def radical_mod_p(Ls, e, p):
    """Basis (mod p) of rad(Lambda/p Lambda) for a ZZ-order Lambda.

    Ls are the integer matrices of left multiplication by a ZZ-basis of
    Lambda (acting on coordinate columns), e the coordinates of 1.  This is
    the characteristic-p algorithm of Friedl-Ronyai (as in SageMath's
    radical_basis), run with integer matrices and characteristic
    polynomials over ZZ reduced mod p.
    """
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
        Bs = [sum(ZZ(ci) * b for ci, b in zip(c, Bs)) if any(c) else 0 * Bs[0]
              for c in C]
        s *= p
    return [vector(F, list(b * e)) for b in Bs]


def center_dim_mod_p(Ls, Rs, p):
    """Dimension of the center of Lambda/p Lambda."""
    F = GF(p)
    n = Ls[0].nrows()
    # x is central iff L_x b = R_x b for all basis b, i.e. sum x_i (L_i - R_i)
    rows = [vector(F, list((L - R).list())) for L, R in zip(Ls, Rs)]
    return matrix(F, rows).left_kernel().dimension()


for D in [d for d in range(2, 200) if Integer(d).is_squarefree()]:
    B = algebra_with_discriminant(D)
    O = B.maximal_order()
    basis = list(O.basis())
    one = B(1)

    def co(x):
        return vector(QQ, list(x))   # coordinates in 1, i, j, k

    Ob = lattice([co(x) for x in basis])

    def elt(v):
        return sum(c * g for c, g in zip(v, [B(1)] + list(B.gens())))

    def product(L1, L2):
        return lattice([co(elt(u) * elt(v)) for u in L1.rows() for v in L2.rows()])

    Bm = matrix(QQ, [co(x) for x in basis])
    Binv = Bm.inverse()
    Ls = [matrix(QQ, [list(co(x * y) * Binv) for y in basis]).transpose()
          .change_ring(ZZ) for x in basis]
    Rs = [matrix(QQ, [list(co(y * x) * Binv) for y in basis]).transpose()
          .change_ring(ZZ) for x in basis]
    e1 = vector(ZZ, list(co(one) * Binv))
    gram = matrix(QQ, [[(x * y).reduced_trace() for y in basis] for x in basis])
    ok(abs(gram.det()) == D**2, D)                 # d(O/Z) = D^2
    # dual lattice for the reduced trace = inverse different
    dual_coeffs = gram.inverse()
    dual = lattice([co(sum(c * y for c, y in zip(row, basis)))
                    for row in dual_coeffs.rows()])
    diff = Ob
    for p in Integer(D).prime_divisors():
        rad = radical_mod_p(Ls, e1, p)
        ok(len(rad) == 2, (D, p))                  # [O : P] = p^2
        Pp = lattice([co(p * x) for x in basis]
                     + [co(sum(ZZ(c) * y for c, y in zip(v, basis))) for v in rad])
        ok(same(product(Ob, Pp), Pp) and same(product(Pp, Ob), Pp))  # 2-sided
        ok(same(product(Pp, Pp), lattice([co(p * x) for x in basis])))  # P^2=pO
        nrs = [elt(v).reduced_norm() for v in Pp.rows()]
        trs = [(elt(u) * elt(v).conjugate()).reduced_trace()
               for u in Pp.rows() for v in Pp.rows()]
        ok(gcd(nrs + trs) == p, (D, p))            # nr P_p = pZ
        diff = product(diff, Pp)
    ok(same(product(diff, dual), Ob) and same(product(dual, diff), Ob), D)
    for p in prime_range(30):
        if D % p == 0:
            continue
        ok(len(radical_mod_p(Ls, e1, p)) == 0, (D, p))   # O/pO semisimple
        ok(center_dim_mod_p(Ls, Rs, p) == 1, (D, p))     # simple: M_2(F_p)
    # M_2(O): reduced trace form, discriminant D^8
    big = []
    for r in range(2):
        for c in range(2):
            for x in basis:
                big.append((r, c, x))

    def mtr(u, v):
        # trace of the product of the elementary matrices E_rc x and E_st y
        (r, c, x), (s, t, y) = u, v
        return (x * y).reduced_trace() if (c == s and t == r) else 0
    gram2 = matrix(QQ, [[mtr(u, v) for v in big] for u in big])
    ok(abs(gram2.det()) == D**8, D)

print(f'ok s32_local_invariants: {N} checks')
