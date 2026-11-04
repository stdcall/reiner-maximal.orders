"""Reduced norms over global fields (Section 33).

Checked exactly:

* (33.1) (pp. 282-283): the identity
  [[0,1],[1,0]] = [[1,-1],[0,1]] [[1,0],[1,1]] [[1,1],[0,-1]].
* (33.12) (pp. 287-288), the correction of the range of t and of the bound
  for lambda (corrections.json, "where 0 < t <= n - 1"): for every prime
  power q < 200, 2 <= n < 60, divisor s of n with s < n, and 1 <= t <= n - 1
  lambda = (q^s - 1) t (q - 1) satisfies the corrected bound
  lambda <= (q^{n/2} - 1)(q - 1)(n - 1) (compared exactly, squaring where
  n is odd), the corrected bound is < q^n - 1, and q^n - 1 does not divide
  lambda.  Refuted printed readings: t = n - 1 occurs (i = 0, j = n - 1), and
  for n = 2 the printed bound (q^{n/2} - 1)(q - 1)(n - 2) is 0 < lambda; for
  many (q, n) the printed bound is exceeded by t = n - 1.  The general
  statement is proved in checks/lean/ReinerMaximalOrders/UnramifiedNormBound.lean.
  The combinatorial core of (33.12), at the level of residue fields: for
  every prime power q <= 9, 2 <= n <= 6 (q^n <= 4096) and every
  x in F_{q^n}^*, some x w^{j(q-1)}, 0 <= j < n, generates F_{q^n} over F_q
  (w a generator of F_{q^n}^*), and the proper ones among these fields are
  pairwise distinct; N(w^{q-1}) = 1.
* (33.13) (pp. 288-289), the construction for n not dividing r = v(beta):
  for p in {2, 3, 5}, m in {2, ..., 5}, 1 <= s <= 4 with (m, s) = 1 and units
  u in {1, -1, 2}, the polynomial X^m + p^t X + (-1)^m beta, beta = p^s u,
  t = s + 1, is irreducible over Q_p (PARI factorpadic) with constant term
  (-1)^m beta, so beta is a norm from a separable extension of degree m.
* Hasse-Schilling-Maass (33.15) (pp. 289-290): for every quaternion algebra
  (a, b)_QQ with a, b squarefree, |a|, |b| <= 12, and every integer
  alpha with 1 <= |alpha| <= 40: if alpha is in U(A) (alpha > 0 when
  a, b < 0), an explicit x in A with nr x = alpha is found (PARI qfsolve,
  verified by evaluation); if A is definite the norm form is positive
  definite, so no alpha < 0 is a reduced norm (local obstruction at the
  ramified real prime, (33.4)).  Over K = QQ(sqrt 2) for
  A = (-1, -(1 + sqrt 2)), ramified at exactly one real prime P_1: explicit
  elements of reduced norm alpha c^2 (c in K^*) for alpha in a list of
  elements of U(A), some negative at the other real prime; nr A is positive
  at P_1.
* Exercise 33.4 (p. 292): (QQ(sqrt d)/QQ, sigma, a) is a (totally) definite
  quaternion algebra iff d < 0 and a < 0, for squarefree |d|, |a| <= 30.

Not established: Krasner's Lemma (33.8) and the general theorems; only the
listed algebras, fields and ranges.
"""
from sage.all import (QQ, ZZ, GF, Integer, DiagonalQuadraticForm, NumberField,
                      PolynomialRing, QuaternionAlgebra, hilbert_symbol, matrix,
                      pari, prime_range, sqrt)
import itertools

N = 0


def ok(cond, msg=''):
    global N
    assert cond, msg
    N += 1


# --- (33.1) ----------------------------------------------------------------
ok(matrix(ZZ, [[1, -1], [0, 1]]) * matrix(ZZ, [[1, 0], [1, 1]])
   * matrix(ZZ, [[1, 1], [0, -1]]) == matrix(ZZ, [[0, 1], [1, 0]]))

# --- (33.12): the bound ----------------------------------------------------
prime_powers = [q for q in range(2, 200) if Integer(q).is_prime_power()]
printed_exceeded = 0
for q in prime_powers:
    for n in range(2, 60):
        Q = q**n - 1
        c = (q - 1) * (n - 1)
        # corrected bound B = (q^{n/2} - 1) c < q^n - 1  <=>  c < q^{n/2} + 1
        ok(c - 1 < 0 or (c - 1)**2 < q**n, (q, n))
        for s in Integer(n).divisors():
            if s == n:
                continue
            for t in range(1, n):
                lam = (q**s - 1) * t * (q - 1)
                # lam <= (q^{n/2} - 1) c  <=>  (lam / c + 1)^2 <= q^n
                ok((QQ(lam) / c + 1)**2 <= q**n, (q, n, s, t))
                ok(0 < lam < Q and lam % Q != 0, (q, n, s, t))
            # printed bound with (n - 2) and the excluded t = n - 1
            t = n - 1
            lam = (q**s - 1) * t * (q - 1)
            if (QQ(lam) / ((q - 1) * (n - 2)) + 1)**2 > q**n if n > 2 else True:
                printed_exceeded += 1
    # n = 2: printed range 0 < t < 1 is empty, printed bound 0
    ok((q - 1)**2 > 0 * (q - 1) * (2 - 2))
ok(printed_exceeded > 0)


# --- (33.12): residue field core -------------------------------------------
def generates(x, q, n):
    """x generates F_{q^n} over F_q iff x^(q^s) != x for proper divisors s."""
    return all(x**(q**s) != x for s in Integer(n).divisors() if s < n)


for q in [2, 3, 4, 5, 7, 8, 9]:
    for n in range(2, 7):
        if q**n > 4096:
            continue
        F = GF(q**n, 'z')
        w = F.multiplicative_generator()
        ok(w**((q - 1) * sum(q**i for i in range(n))) == 1)
        for x in F:
            if x == 0:
                continue
            ys = [x * w**(j * (q - 1)) for j in range(n)]
            ok(any(generates(y, q, n) for y in ys), (q, n, x))
            proper = []
            for y in ys:
                if not generates(y, q, n):
                    # the subfield generated by y: smallest s | n, y^(q^s) = y
                    s = min(d for d in Integer(n).divisors() if y**(q**d) == y)
                    proper.append(s)
            ok(len(proper) == len(set(proper)), (q, n, x))

# --- (33.13) ---------------------------------------------------------------
R = PolynomialRing(QQ, 'X')
X = R.gen()
for p in [2, 3, 5]:
    for m in range(2, 6):
        for s in range(1, 5):
            if Integer(m).gcd(s) != 1:
                continue
            for u in [1, -1, 2]:
                if u % p == 0:
                    continue
                beta = p**s * u
                t = s + 1
                f = X**m + p**t * X + (-1)**m * beta
                fac = pari(f).factorpadic(p, 30)
                degrees = [pari(fac[0][i]).poldegree() for i in range(len(fac[0]))]
                ok(degrees == [m], (p, m, s, u))
                ok(f(0) == (-1)**m * beta)


# --- Hasse-Schilling-Maass over QQ ------------------------------------------
def squarefree_range(bound):
    return [d for d in range(-bound, bound + 1)
            if d not in (0, 1) and Integer(d).is_squarefree()]


vals = squarefree_range(12)
for a in vals:
    for b in vals:
        nf = DiagonalQuadraticForm(QQ, [1, -a, -b, a * b])   # nr of x0+x1i+x2j+x3k
        definite = a < 0 and b < 0
        ok(definite == (hilbert_symbol(a, b, -1) == -1))
        if definite:
            ok(nf.is_positive_definite())
        for alpha in list(range(-40, 0)) + list(range(1, 41)):
            if definite and alpha < 0:
                continue
            x = nf.solve(alpha)
            ok(nf(x) == alpha, (a, b, alpha))

# --- Hasse-Schilling-Maass over QQ(sqrt 2), one real prime ramified ---------
Kx = PolynomialRing(QQ, 'y')
K = NumberField(Kx.gen()**2 - 2, 'r')
r = K.gen()
A = QuaternionAlgebra(K, -1, -(1 + r))
emb = K.real_embeddings()
P1 = [e for e in emb if e(r) > 0][0]
P2 = [e for e in emb if e(r) < 0][0]
fin, inf = A.ramified_places()
ok(len(inf) == 1 and inf[0](r) > 0 and len(fin) == 1)   # ramified at P_1 only
ok(P1(K(-1)) < 0 and P1(-(1 + r)) < 0 and P2(-(1 + r)) > 0)
# nr(x0 + x1 i + x2 j + x3 k) = x0^2 + x1^2 + (1 + r)(x2^2 + x3^2): positive at P1
targets = [1 + r, -1 + 2 * r, 3 + r, 2 * r - 1, 5 * r - 3, 1 + 3 * r, 7 - r]
for alpha in targets:
    ok(P1(alpha) > 0)
found = {}
for v in itertools.product(range(-2, 3), repeat=4):
    for w in itertools.product([0, 1], repeat=4):
        xs = [v[i] + w[i] * r for i in range(4)]
        nr = xs[0]**2 + xs[1]**2 + (1 + r) * (xs[2]**2 + xs[3]**2)
        if nr == 0:
            continue
        for alpha in targets:
            if alpha not in found and (nr / alpha).is_square():
                found[alpha] = xs
    if len(found) == len(targets):
        break
for alpha in targets:
    xs = found[alpha]
    nr = xs[0]**2 + xs[1]**2 + (1 + r) * (xs[2]**2 + xs[3]**2)
    ok((nr / alpha).is_square(), alpha)    # alpha = nr(x / c), c^2 = nr / alpha
ok(any(P2(alpha) < 0 for alpha in targets))
# alpha with alpha_{P1} < 0 is not a norm: the form is positive definite at P1
ok(all(P1(c) > 0 for c in [1, 1 + r]))

# --- Exercise 33.4 -------------------------------------------------------------
for d in squarefree_range(30):
    for a in squarefree_range(30):
        definite = hilbert_symbol(d, a, -1) == -1
        ok(definite == (d < 0 and a < 0), (d, a))

print(f'ok s33_reduced_norms: {N} checks')
