"""Exact checks of Chapter 3, sections 12-14 (maximal orders in local
skewfields), pp. 135-153.

Section 12.
  * (12.2): if f = alpha_0 X^n + ... + alpha_n is irreducible over Q_p then
    v(alpha_i) >= min(v(alpha_0), v(alpha_n)); Lemma (12.9): if f is monic
    and irreducible, v(alpha_k) >= (k/n) v(alpha_n).  All squarefree
    polynomials with alpha_0 in {1, p} and alpha_1, ..., alpha_n of the form
    +-p^e u (e in {0, 1, 2}, u in {1, 2}) for n = 2, 3, in {1, -1, p, p^2}
    for n = 4, p = 2, 3, 5; irreducibility over Q_p by Sage; both bounds fail
    for some reducible polynomials (so the hypothesis is needed).
  * (12.5), (12.6), (12.8): in the definite quaternion algebras ramified at
    p = 2, 3, 5, 7, 11, 13 (Sage's QuaternionAlgebra(p)), for the elements
    sum c_i b_i / p^t (b_i a basis of the maximal order, |c_i| <= 2,
    t = 0, 1): nr(a) in Z_(p) implies tr(a) in Z_(p) and a in Delta_(p);
    w(a) = v_p(nr a)/2 satisfies w(a + b) >= min(w(a), w(b)).  For a prime
    q not dividing the discriminant, elements with nr in Z_(q) and tr not
    in Z_(q) exist (the skewfield hypothesis is needed).
Section 13.
  * (13.3), (13.7), Exercises 13.3, 13.4: for the same algebras, e = 2 and
    f = 2: the ideal p = pi_D Delta + p Delta has index p^2, p^2 = p Delta,
    v(nr pi_D) = 1 = sqrt(f/e), v(N pi_D) = 2 = f.
  * Proof of (13.3), p. 140 (correction "b_j in D"): v_D(a) = 2 v_p(a) for
    a in Q, so elements of K never have incongruent values mod e = 2.
  * Proof of (13.3), p. 141 (correction x = u (pi^k b_j)): in the model
    D = (W/Q, theta, 2), W = Q((-3)^(1/2)), with x = omega pi_D, b_1 = pi_D,
    the corrected unit u = x pi_D^(-1) = omega gives x - u b_1 = 0, while the
    printed u' with x = pi_D u' gives x - u' b_1 = (omega - omega^2) pi_D of
    the same value v_D(x) = 1 (no approximation; refuted).
Section 14.
  * (14.1) and its proof: N: (o_W / p^k)^* -> (Z/p^k)^* is onto for W
    unramified at p of degree f (Q(i): p = 3, 7; Q((-3)^(1/2)): p = 2, 5;
    the cyclic cubic field of conductor 7: p = 2, 3, 5), k = 1, 2;
    exactly (q^f - 1)/(q - 1) elements of F_(q^f) have norm 1 (q <= 7,
    f <= 3); N(pi^k x_0) = pi^(kf) N(x_0) (correction of the exponent).
  * (14.5), (14.6), (14.7): the model over the centre K = Q((-7)^(1/2)),
    W = Q(zeta_7), theta: zeta -> zeta^(2^r) (r = 1, 2), pi = 2 (a prime
    element at a prime of K over 2, where q = 2 and W is unramified of
    degree 3): (pi_D^*)^3 = 2, pi_D^* omega^* (pi_D^*)^(-1) = (omega^(q^r))^*,
    the matrices commuting with omega^* are diagonal, those commuting also
    with pi_D^* are scalars in K, and sum alpha_j^* (pi_D^*)^j has the
    printed form (14.7); Exercise 14.2: the conjugates of omega include
    omega^(q^i) for all i.
  * Proof of (14.6), p. 149 (correction of the sign): for generic entries
    (theta^i(alpha_j) independent indeterminates) and alpha_0 = pi beta_0,
    det a = (-1)^(n-1) pi prod theta^i(alpha_1) mod pi^2, n = 2, ..., 5,
    and det a = prod theta^i(alpha_0) mod pi; the printed congruence
    without the sign is refuted for n even.
  * (14.9), Lemma (14.8): for Lambda = sum o_W pi_D^j in the models
    (W/Q, theta, 2) with W = Q((-3)^(1/2)) (n = 2) and W the cyclic cubic
    field of conductor 7 (n = 3), tr(sum alpha_j pi_D^j) = T(alpha_0),
    v_2 d(Lambda / Z) = n(n - 1), tr(pi_D^(-(n-1)) Lambda) is 2-integral and
    tr(pi_D^(-n) Lambda) is not; pi_D^(-(n-1)) = pi^(-1) pi_D (correction).
  * Exercise 14.1 for a = i in (-1, -1)_Q: ten distinct zeros
    (j + c) i (j + c)^(-1) of X^2 + 1.
  * Exercise 14.3: for the Hurwitz order Lambda at 2, d = 4 = 2^(n(n-1)),
    pi_D = 1 + i, Lambda / pi_D Lambda has 4 elements, omega =
    (-1 + i + j + k)/2 satisfies omega^2 + omega + 1 = 0, the inertia field
    Q_2(omega) is unramified, and {1, omega, pi_D, omega pi_D} is a
    Z_(2)-basis of Lambda.
  * Exercise 14.4 (correction Phi_4 -> Phi_8): X^4 + 1 = Phi_8, not Phi_4;
    -2 is a square in Z_3; Phi_8 = (X^2 - aX - 1)(X^2 + aX - 1) with
    a = zeta + zeta^3, the factors are irreducible over Q_3 and have the
    printed roots.
  * Exercise 14.5: char. pol. pi_D^* = X^n - pi and det pi_D^* =
    (-1)^(n-1) pi for n = 2, ..., 8; det alpha^* = N_(W/K) alpha in the
    model.
What is NOT established: the general theorems; local statements are
checked on global models (number fields, quaternion algebras over Q) at
the indicated primes.
"""
from itertools import product

from sage.all import (GF, QQ, ZZ, CyclotomicField, NumberField, PolynomialRing,
                      QuaternionAlgebra, Qp, Zp, cyclotomic_polynomial,
                      identity_matrix, matrix, prod, randint, set_random_seed,
                      vector)

set_random_seed(20261104)
N = 0


def check(condition, label):
    global N
    assert condition, label
    N += 1


X = PolynomialRing(QQ, 'X').gen()


def v(a, p):
    return QQ(a).valuation(p) if a != 0 else 10**9


# --------------------------------------------------------------- Section 12
for p in [2, 3, 5]:
    Rp = Qp(p, 40)
    coeffs = sorted({s * u * p**e for s in [1, -1] for u in [1, 2]
                     for e in [0, 1, 2]})
    seen_violation = [False, False]
    small = [1, -1, p, p**2]
    for n in [2, 3, 4]:
        for cs in product(coeffs if n < 4 else small, repeat=n):
            for a0 in [1, p]:
                f = a0 * X**n + sum(cs[i] * X**(n - 1 - i) for i in range(n))
                al = [a0] + list(cs)
                if f.discriminant() == 0:
                    continue
                irred = len(f.change_ring(Rp).factor()) == 1
                b1 = all(v(al[i], p) >= min(v(al[0], p), v(al[n], p))
                         for i in range(n + 1))
                if irred:
                    check(b1, '(12.2)')
                elif not b1:
                    seen_violation[0] = True
                if a0 == 1:
                    b2 = all(v(al[k], p) * n >= k * v(al[n], p)
                             for k in range(1, n + 1))
                    if irred:
                        check(b2, 'Lemma (12.9)')
                    elif not b2:
                        seen_violation[1] = True
    check(all(seen_violation), 'reducible polynomials violate the bounds')

for p in [2, 3, 5, 7, 11, 13]:
    A = QuaternionAlgebra(p)
    O = A.maximal_order()
    Ob = O.basis()
    Omat = matrix(QQ, [list(b) for b in Ob])
    sample = []
    for t in [0, 1]:
        for cs in product(range(-2, 3), repeat=4):
            a = sum(c * b for c, b in zip(cs, Ob)) / p**t
            sample.append(a)
    for a in sample:
        if a == 0:
            continue
        if v(a.reduced_norm(), p) >= 0:
            check(v(a.reduced_trace(), p) >= 0, '(12.5) nr integral => tr')
            cofs = vector(QQ, list(a)) * Omat.inverse()
            check(all(v(c, p) >= 0 for c in cofs), '(12.8) a in Delta_(p)')
    for _ in range(400):
        a, b = sample[randint(0, len(sample) - 1)], sample[randint(0, len(sample) - 1)]
        if a == 0 or b == 0 or a + b == 0:
            continue
        w = lambda z: QQ(v(z.reduced_norm(), p)) / 2
        check(w(a + b) >= min(w(a), w(b)), '(12.6) w is a valuation')
    # e and f
    pis = [a for a in sample if a != 0 and v(a.reduced_norm(), p) == 1
           and all(v(c, p) >= 0 for c in vector(QQ, list(a)) * Omat.inverse())]
    piD = pis[0]
    gens = [piD * b for b in Ob] + [p * b for b in Ob]
    Pl = matrix(QQ, [list(g) for g in gens]).row_module(ZZ)
    Ol = Omat.row_module(ZZ)
    check(Pl.index_in(Ol) == p**2, '(13.3) f = 2: card Delta/p = p^2')
    P2 = matrix(QQ, [list(g * h) for g in [piD * b for b in Ob]
                     for h in [piD * b for b in Ob]] +
                [list(p * g) for g in gens]).row_module(ZZ)
    pO = matrix(QQ, [list(p * b) for b in Ob]).row_module(ZZ)
    check(P2 == pO, '(13.3) e = 2: p^2 = p Delta')
    check(v(piD.reduced_norm(), p) == 1 and v(piD.reduced_norm()**2, p) == 2,
          'Exercise 13.3: v(nr pi_D) = 1, v(N pi_D) = 2')
    for c in [QQ(p), QQ(1) / p, QQ(3 * p**2), QQ(5) / 7]:
        check(v(A(c).reduced_norm(), p) % 2 == 0,
              'correction (13.3): v_D(K^*) = eZ')
# a split prime: nr in Z_(q) but tr not
A = QuaternionAlgebra(QQ, -1, -1)
qi, qj, qk = A.gens()
found = any(v((c0 + c1 * qi + c2 * qj + c3 * qk).reduced_norm() / 9, 3) >= 0
            and v((c0 + c1 * qi + c2 * qj + c3 * qk).reduced_trace() / 3, 3) < 0
            for c0, c1, c2, c3 in product(range(-4, 5), repeat=4))
check(found, '(12.5) needs a skewfield: (-1,-1) at 3')

# --------------------------------------------------------------- models


def it(theta, i, a):
    """theta^i(a)."""
    for _ in range(i):
        a = theta(a)
    return a


def cyclic_model(W, theta, n, pi):
    """alpha -> alpha^*, pi_D^* of the proof of (14.6), over W."""
    def star(a):
        return matrix.diagonal(W, [it(theta, i, a) for i in range(n)])
    P = matrix(W, n, n, 0)
    for i in range(n - 1):
        P[i, i + 1] = 1
    P[n - 1, 0] = pi
    return star, P


# n = 2: W = Q((-3)^(1/2)), p = 2 inert, theta = conjugation
W2 = NumberField(X**2 + X + 1, 'w')
om = W2.gen()
th2 = W2.automorphisms()[1]
star2, P2m = cyclic_model(W2, th2, 2, 2)
check(P2m**2 == 2 and P2m * star2(om) * P2m.inverse() == star2(th2(om)),
      'model n = 2')
x_el = star2(om) * P2m
check(QQ(x_el.det()).valuation(2) == 1,
      'v_D(omega pi_D) = 1')
u_corr = x_el * P2m.inverse()
check(u_corr == star2(om) and x_el - u_corr * P2m == 0,
      'corrected (13.3): x - u b_1 = 0')
u_print = P2m.inverse() * x_el
check(u_print == star2(om**2), "printed u' = omega^2")
diff = x_el - u_print * P2m
check(diff == star2(om - om**2) * P2m
      and QQ(diff.det()).valuation(2) == 1, "printed reading: no improvement")

# --------------------------------------------------------------- Section 14
unram = [(X**2 + 1, 3), (X**2 + 1, 7), (X**2 + X + 1, 2), (X**2 + X + 1, 5),
         (X**3 + X**2 - 2 * X - 1, 2), (X**3 + X**2 - 2 * X - 1, 3),
         (X**3 + X**2 - 2 * X - 1, 5)]
for f, p in unram:
    Wf = NumberField(f, 'a')
    fdeg = Wf.degree()
    check(len(Wf.primes_above(p)) == 1 and Wf.disc() % p != 0, 'p inert')
    ib = Wf.integral_basis()
    for k in [1, 2]:
        if p**(fdeg * k) > 3000:
            continue
        mod = p**k
        norms = set()
        for cs in product(range(mod), repeat=fdeg):
            a = sum(c * b for c, b in zip(cs, ib))
            nm = ZZ(a.norm()) % mod
            if nm % p != 0:
                norms.add(nm)
        units = {c for c in range(mod) if c % p != 0}
        check(norms == units, '(14.1) norm onto units mod p^k')
    x0 = Wf.random_element(num_bound=5)
    for k in range(4):
        check((p**k * x0).norm() == p**(k * fdeg) * x0.norm(),
              'corrected (14.1): N(pi^k x_0) = pi^(kf) N(x_0)')
for q in [2, 3, 4, 5, 7]:
    for f in [2, 3]:
        F = GF(q**f, 'g')
        e = (q**f - 1) // (q - 1)
        cnt = sum(1 for z in F if z != 0 and z**e == 1)
        check(cnt == e, '(14.1) proof: norm-one elements')

# the model of (14.5)-(14.7) over K = Q((-7)^(1/2))
W7 = CyclotomicField(7)
z = W7.gen()
gauss = z + z**2 + z**4
check(gauss**2 + gauss + 2 == 0, 'K = Q((-7)^(1/2)) inside Q(zeta_7)')
for r in [1, 2]:
    th = W7.hom([z**(2**r)])
    check(th(gauss) == gauss, 'theta fixes K')
    star, P = cyclic_model(W7, th, 3, 2)
    check(P**3 == 2 and P * star(z) * P.inverse() == star(z**(2**r)),
          '(14.5) pi_D^n = pi, pi_D omega pi_D^(-1) = omega^(q^r)')
    exps = sorted({(2**(r * i)) % 7 for i in range(3)})
    check(exps == [1, 2, 4], 'Exercise 14.2')
    # commutant of omega^*
    rows = []
    for M in [star(z)]:
        for i in range(3):
            for j in range(3):
                row = [0] * 9
                for k in range(3):
                    row[3 * i + k] += M[k, j]
                    row[3 * k + j] -= M[i, k]
                rows.append(row)
    ker = matrix(W7, rows).right_kernel()
    check(ker.dimension() == 3 and all(
        b[1] == b[2] == b[3] == b[5] == b[6] == b[7] == 0 for b in ker.basis()),
        '(14.6) commutant of omega^* is diagonal')
    # diagonal commuting with P: alpha^* with theta(alpha) = alpha
    for a in [z, z + z**3, gauss, 1 + z**2]:
        commutes = star(a) * P == P * star(a)
        check(commutes == (th(a) == a), '(14.6) centre K')
    al = [W7.random_element(num_bound=3) for _ in range(3)]
    a = sum(star(al[j]) * P**j for j in range(3))
    printed = matrix(W7, 3, 3, lambda i, j: it(th, i, al[j - i]) if j >= i
                     else 2 * it(th, i, al[3 + j - i]))
    check(a == printed, '(14.7) matrix form')
    Wrel = W7.relativize(gauss, 'b')
    to_abs, from_abs = Wrel.structure()
    rel_norm = to_abs(Wrel(from_abs(al[0]).relative_norm()))
    check(star(al[0]).det() == rel_norm,
          'Exercise 14.5: det alpha^* = N_(W/K) alpha')
K7 = NumberField(X**2 + X + 2, 'g')
P_ab = K7.primes_above(2)
check(len(P_ab) == 2 and all(K7(2).valuation(P) == 1 for P in P_ab),
      'pi = 2 is a prime element at the primes of K over 2')

# C072: generic determinant, n = 2..5
for n in range(2, 6):
    names = [f'a{i}_{j}' for i in range(n) for j in range(n)] + \
            [f'b{i}' for i in range(n)] + ['p']
    Rg = PolynomialRing(ZZ, names)
    gen = dict(zip(names, Rg.gens()))
    pi = gen['p']

    def ent(i, j, sub0):
        jj = (j - i) % n
        val = gen[f'a{i}_{jj}']
        if jj == 0 and sub0:
            val = pi * gen[f'b{i}']
        return val if j >= i else pi * val
    Mgen = matrix(Rg, n, n, lambda i, j: ent(i, j, False))
    d0 = Mgen.det()
    check(d0.subs(p=0) == prod(gen[f'a{i}_0'] for i in range(n)),
          '(14.6): det a = N alpha_0 mod pi')
    Ms = matrix(Rg, n, n, lambda i, j: ent(i, j, True))
    ds = Ms.det()
    c0 = ds.subs(p=0)
    c1 = (ds.derivative(pi)).subs(p=0)
    target = prod(gen[f'a{i}_1'] for i in range(n))
    check(c0 == 0 and c1 == (-1)**(n - 1) * target,
          'corrected (14.6): det a = (-1)^(n-1) pi N alpha_1 mod pi^2')
    if n % 2 == 0:
        check(c1 != target, 'printed congruence without sign refuted')

# (14.9) in the models n = 2, 3 over Q, pi = 2.
W3 = NumberField(X**3 + X**2 - 2 * X - 1, 'c')
th3 = [s for s in W3.automorphisms() if s(W3.gen()) != W3.gen()][0]
for Wm, thm, n in [(W2, th2, 2), (W3, th3, 3)]:
    star, P = cyclic_model(Wm, thm, n, 2)
    ob = Wm.integral_basis()
    basis = [star(b) * P**j for j in range(n) for b in ob]
    tr = lambda M: QQ(M.trace())
    al = [Wm.random_element(num_bound=4) for _ in range(n)]
    a = sum(star(al[j]) * P**j for j in range(n))
    check(tr(a) == al[0].trace(), '(14.9) proof: tr = T(alpha_0)')
    G = matrix(QQ, len(basis), len(basis), lambda r, c: tr(basis[r] * basis[c]))
    dW = Wm.disc()
    check(G.det().valuation(2) == n * (n - 1) and dW % 2 != 0,
          '(14.9) d(Delta) = P^(n(n-1))')
    check(P.inverse()**(n - 1) == P / 2, 'corrected: pi_D^(-(n-1)) = pi^(-1) pi_D')
    check(all(tr(P.inverse()**(n - 1) * b).valuation(2) >= 0 for b in basis),
          '(14.9) tr(pi_D^(-(n-1)) Delta) in R')
    check(any(tr(P.inverse()**n * b).valuation(2) < 0 for b in basis),
          '(14.9) tr(pi_D^(-n) Delta) not in R')

# Exercise 14.1
zeros = {(qj + c) * qi * (qj + c)**(-1) for c in range(10)}
check(len(zeros) == 10 and all(t**2 == -1 for t in zeros), 'Exercise 14.1')

# Exercise 14.3
Hur = [(1 + qi + qj + qk) / 2, qi, qj, qk]
Hmat = matrix(QQ, [list(b) for b in Hur])
G = matrix(QQ, 4, 4, lambda r, c: (Hur[r] * Hur[c]).reduced_trace())
check(abs(G.det()) == 4 == 2**(2 * 1), 'Exercise 14.3: d = 4')
piD = 1 + qi
check(piD.reduced_norm() == 2, 'pi_D = 1 + i')
Lmod = Hmat.row_module(ZZ)
Pid = matrix(QQ, [list(piD * b) for b in Hur]).row_module(ZZ)
check(Pid.index_in(Lmod) == 4, 'Lambda/pi_D Lambda has 4 elements')
w_ = (-1 + qi + qj + qk) / 2
check(w_**2 + w_ + 1 == 0 and w_**3 == 1, 'omega primitive cube root of 1')
check(vector(QQ, list(w_ - 1)) not in Pid and vector(QQ, list(w_)) not in Pid
      and vector(QQ, list(w_**2 + w_ + 1)) in Pid,
      'residue field F_4 = F_2(omega-bar)')
check(PolynomialRing(GF(2), 'T')([1, 1, 1]).is_irreducible(),
      'Q_2(omega) unramified')
Bnew = matrix(QQ, [list(b) for b in [A(1), w_, piD, w_ * piD]])
coords = Bnew * Hmat.inverse()
check(all(c in ZZ for c in coords.list()) and coords.det() % 2 != 0,
      'Exercise 14.3: Z_(2)-basis 1, omega, pi_D, omega pi_D')

# Exercise 14.4
Z8 = CyclotomicField(8)
zz = Z8.gen()
a8 = zz + zz**3
Y = PolynomialRing(Z8, 'Y').gen()
check(a8**2 == -2, 'a^2 = -2')
check((Y**2 - a8 * Y - 1) * (Y**2 + a8 * Y - 1) == Y**4 + 1,
      'Exercise 14.4 factorization')
check(Y**2 - a8 * Y - 1 == (Y - zz) * (Y - zz**3)
      and Y**2 + a8 * Y - 1 == (Y - zz**5) * (Y - zz**7), 'printed roots')
check(cyclotomic_polynomial(8, 'X') == X**4 + 1 and cyclotomic_polynomial(4, 'X')
      == X**2 + 1, 'correction Phi_4 -> Phi_8')
T3 = PolynomialRing(Zp(3, 30), 'T').gen()
check(len((T3**2 + 2).roots()) == 2, '-2 is a square in Z_3')
check(not GF(3)(2).is_square(), 'factors irreducible over Q_3 (disc 2)')

# Exercise 14.5
Pp = PolynomialRing(QQ, 'pp')
pp = Pp.gen()
for n in range(2, 9):
    M = matrix(Pp, n, n, 0)
    for i in range(n - 1):
        M[i, i + 1] = 1
    M[n - 1, 0] = pp
    check(M.det() == (-1)**(n - 1) * pp, 'Exercise 14.5: det pi_D^*')
    check(M.charpoly('X') == PolynomialRing(Pp, 'X').gen()**n - pp,
          'char pol pi_D^* = X^n - pi')
    check(M**n == pp * identity_matrix(Pp, n), '(pi_D^*)^n = pi')

print(f'ok s12_14_local_skewfields: {N} checks')
