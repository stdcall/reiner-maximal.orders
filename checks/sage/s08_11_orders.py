"""Exact checks of Chapter 2, sections 8-11 (orders, reduced norms and
traces, existence of maximal orders, localization), pp. 108-134.

Section 8.
  * (8.1), (8.2), p. 109: the left and right orders O_l(M), O_r(M) of the
    full Z-lattice M = Z E_11 + Z E_12/2 + 3Z E_21 + Z E_22 in M_2(Q),
    computed as the lattices of solutions of the conditions x m_k in M
    (m_k a basis of M), contain 1, are closed under multiplication, are full
    lattices, and O_l(M) M = M = M O_r(M).
  * (8.7): the discriminant of M_n(Z) is +-1 (n = 2, 3); by Exercise 10.3
    no larger order exists, so M_n(Z) is maximal in M_n(Q).
Section 9.
  * Example (9.4), p. 115: h(i) = diag(i, -i), h(j) = [[0, 1], [-1, 0]]
    satisfy the quaternion relations; red. char. pol. alpha + beta j =
    X^2 - (alpha + alpha-bar) X + (alpha alpha-bar + beta beta-bar), equal
    to the reduced characteristic polynomial computed by Sage.
  * (9.5)-(9.7): char. pol._(A/K) a = (red. char. pol. a)^n, T = n tr,
    N = nr^n, for the quaternion algebras (-1, -1), (-1, -3), (2, 5) over Q
    and for M_3(Q).
  * (9.9): the reduced trace form is nondegenerate and associative.
  * (9.10)(ii), (iii) and Exercise 9.4 for L = Q(2^(1/3)).
  * (9.14)-(9.17): for B = (-1, -1) over L = Q(2^(1/2)), viewed over Q:
    char. pol._(B/Q) b = {N_(L/Q) red. char. pol._(B/L) b}^2,
    tr_(B/Q) = T_(L/Q) tr_(B/L), nr_(B/Q) = N_(L/Q) nr_(B/L).
  * Remark after (9.19), p. 121 (correction "nondegenerate"): the
    commutative algebra k[x, y]/(x, y)^2 carries the zero symmetric
    associative form, but every associative bilinear form on it,
    tau(a, b) = lambda(ab), is degenerate (Gram determinant 0 identically
    in lambda), so it is not a Frobenius algebra; the printed condition
    without "nondegenerate" is refuted.
  * (9.31): char. pol. of a_L and a_R coincide in (-1, -1)_Q and in Q S_3;
    Bourbaki's example after (9.32), p. 124: the printed matrices x_L, x_R,
    traces 2 and 1, det (1 + x)_L = 4, det (1 + x)_R = 2, and the algebra
    is associative.
  * Exercise 9.1 for E = Q(zeta_5) in M_4(Q), a = zeta + zeta^(-1).
  * Exercise 9.5 for A = M_2((-1, -1)_Q).
Section 10.
  * Exercise 10.2: d(Z + Zi + Zj + Zk) = 16Z, d(Lambda_0) = 4Z for the
    Hurwitz order Lambda_0 = Lambda + Z(1 + i + j + k)/2, and Lambda_0 is
    the maximal order computed by Sage; (10.1) on its basis products;
    Exercise 10.3: 16 = [Lambda_0 : Lambda]^2 4.
  * Exercise 10.1 (the converse question): for R = F_2[t], A = K (+) K,
    a = (1/t, 1/t) one has tr(a^m) = 0 in R for all m <= 12 while a is not
    integral; so the converse fails in characteristic 2.
  * Faddeev's example, p. 128 (correction r^k -> r^n): for A = T_2(Q),
    T_3(Q) (n = 1, 2), Lambda = T(Z), r = 2, the Lambda_k are orders,
    strictly increasing for k <= 5; r^(n(k+1)) Lambda_k is contained in
    r^n Lambda for every k, while r^(n(k+1)) Lambda_k is not contained in
    r^k Lambda for n < k <= 5 (the printed inference is refuted).
  * Proof of (10.8), p. 130: for the non-hereditary order
    Lambda = {(a, b) in Z (+) Z : a = b mod 2} in Q (+) Q,
    Lambda cap A(1 - e_2) = 2Z e_1 does not contain e_1, and the sequence
    0 -> Lambda' -> Lambda -> Lambda e_2 -> 0 has no Lambda-splitting.
Section 11.
  * (11.5), counterexample in dimension 2: R = Q[x, y] localized at
    (x, y), R^ = Q[[x, y]], A = (x, 1 + y) over Q(x, y), with i^2 = x,
    j^2 = 1 + y = s^2, s = (1 + y)^(1/2) in Q[[y]].  Checked: s exists in
    Q[[y]] (to order 30, coefficients binomial(1/2, k)); 1 + y is not a
    square in Q(y); the elements E_11 = (1 + j/s)/2, E_22 = (1 - j/s)/2,
    E_21 = i E_11, E_12 = E_11 i / x are matrix units over Q(x, s);
    1, i, j, ij lie in the R^-span M of the E_ab, while E_12 does not lie in
    the R^-span of 1, i, j, ij; d(R<i, j>) = -16 x^2 (1 + y)^2 and
    d(M) = -1; tr(i w) lies in x R for all w in R<i, j>, and i/x is not
    integral (nr(i/x) = -1/x).
What is NOT established: the general theorems.  In the counterexample to
(11.5), the maximality of R<i, j> over R is deduced from (11.4), the
discriminant and the fact that (x, 1 + y) is a skewfield over Q(y)((x)),
which rest on the cited theorems, not on this script.
"""
from itertools import product

from sage.all import (GF, QQ, ZZ, CyclotomicField, FunctionField, NumberField,
                      PolynomialRing, PowerSeriesRing, QuaternionAlgebra,
                      SymmetricGroup, binomial, identity_matrix, matrix,
                      prod, randint, set_random_seed, vector)

set_random_seed(20261104)
N = 0


def check(condition, label):
    global N
    assert condition, label
    N += 1


X = PolynomialRing(QQ, 'X').gen()


def E(n, i, j, R=QQ):
    return matrix(R, n, n, {(i, j): 1})


def lattice_rows(mats):
    return matrix(QQ, [m.list() for m in mats]).row_module(ZZ)


def dual_rows(rows):
    """{x : <t, x> in Z for all rows t}, for rows spanning a full lattice."""
    B = matrix(QQ, rows).row_module(ZZ).basis_matrix()
    return (B.inverse().transpose()).row_module(ZZ)


# ---------------------------------------------------------------- Section 8
Mb = [E(2, 0, 0), E(2, 0, 1) / 2, 3 * E(2, 1, 0), E(2, 1, 1)]
Mlat = lattice_rows(Mb)
Bm = matrix(QQ, [m.list() for m in Mb])


def order_of(side):
    """Rows t such that x in O(M) iff <t, x> in Z for all t."""
    rows = []
    Binv = Bm.inverse()
    for k in range(4):
        for c in range(4):
            # coordinate c (in the basis of M) of x m_k (or m_k x),
            # as a linear form in the entries of x
            row = []
            for e in [E(2, a, b) for a in range(2) for b in range(2)]:
                prod_ = e * Mb[k] if side == 'l' else Mb[k] * e
                row.append((vector(QQ, prod_.list()) * Binv)[c])
            rows.append(row)
    return dual_rows(rows)


for side in 'lr':
    O = order_of(side)
    basis = [matrix(QQ, 2, 2, list(v)) for v in O.basis()]
    check(vector(QQ, identity_matrix(QQ, 2).list()) in O, '(8.1) 1 in O(M)')
    check(all(vector(QQ, (a * b).list()) in O for a in basis for b in basis),
          '(8.1) O(M) is a ring')
    check(O.rank() == 4, '(8.1) O(M) is a full lattice')
    act = [a * m if side == 'l' else m * a for a in basis for m in Mb]
    check(all(vector(QQ, x.list()) in Mlat for x in act), 'O(M) M = M')
for n in [2, 3]:
    basis = [E(n, i, j) for i in range(n) for j in range(n)]
    G = matrix(QQ, n * n, n * n, lambda a, b: (basis[a] * basis[b]).trace())
    check(abs(G.det()) == 1, '(8.7) M_n(Z) unimodular discriminant')

# ---------------------------------------------------------------- Section 9
Qi = NumberField(X**2 + 1, 'I')
I = Qi.gen()
hi = matrix(Qi, [[I, 0], [0, -I]])
hj = matrix(Qi, [[0, 1], [-1, 0]])
check(hi**2 == -1 and hj**2 == -1 and hi * hj == -hj * hi,
      'Example (9.4): h is a homomorphism')
H = QuaternionAlgebra(QQ, -1, -1)
qi, qj, _ = H.gens()
for _ in range(10):
    c = [QQ(randint(-9, 9)) / randint(1, 4) for _ in range(4)]
    alpha = c[0] + c[1] * I
    beta = c[2] + c[3] * I
    a = c[0] + c[1] * qi + (c[2] + c[3] * qi) * qj
    hm = matrix(Qi, [[alpha, beta], [-beta.conjugate(), alpha.conjugate()]])
    rc = X**2 - (alpha + alpha.conjugate()) * X \
        + (alpha * alpha.conjugate() + beta * beta.conjugate())
    check(hm.charpoly('X') == rc.change_ring(Qi), 'Example (9.4) charpol')
    check(a.reduced_characteristic_polynomial('X') == rc, '(9.4) vs Sage')
    check(a.reduced_trace() == alpha + alpha.conjugate()
          and a.reduced_norm() == alpha * alpha.conjugate()
          + beta * beta.conjugate(), 'Example (9.4) tr, nr')


def quat_left_right(A, a):
    B = A.basis()
    L = matrix(QQ, [list(a * b) for b in B]).transpose()
    Rm = matrix(QQ, [list(b * a) for b in B]).transpose()
    return L, Rm


for (u, v) in [(-1, -1), (-1, -3), (2, 5)]:
    A = QuaternionAlgebra(QQ, u, v)
    B = A.basis()
    G = matrix(QQ, 4, 4, lambda r, c: (B[r] * B[c]).reduced_trace())
    check(G.det() != 0, '(9.9) nondegenerate')
    for _ in range(6):
        a = A([randint(-5, 5) for _ in range(4)])
        b = A([randint(-5, 5) for _ in range(4)])
        cc = A([randint(-5, 5) for _ in range(4)])
        L, Rm = quat_left_right(A, a)
        rcp = a.reduced_characteristic_polynomial('X')
        check(L.charpoly('X') == rcp**2, '(9.5) char pol = (red)^2')
        check(L.trace() == 2 * a.reduced_trace()
              and L.det() == a.reduced_norm()**2, '(9.7)')
        check(((a * b) * cc).reduced_trace() == (a * (b * cc)).reduced_trace()
              and (a * b).reduced_trace() == (b * a).reduced_trace(),
              '(9.9) symmetric associative')
        check(Rm.charpoly('X') == L.charpoly('X'), '(9.31) a_L, a_R')
for _ in range(6):
    a = matrix(QQ, 3, 3, [randint(-4, 4) for _ in range(9)])
    basis = [E(3, i, j) for i in range(3) for j in range(3)]
    L = matrix(QQ, [(a * b).list() for b in basis]).transpose()
    check(L.charpoly('X') == a.charpoly('X')**3, '(9.5) M_3(Q)')

# (9.10) for L = Q(2^(1/3)).
F = NumberField(X**3 - 2, 'c')
c = F.gen()
basisF = [c**i for i in range(3)]


def tilde(a):
    return matrix(QQ, [list(a * b) for b in basisF]).transpose()


RX = PolynomialRing(QQ, 'X')
Xr = RX.gen()
for _ in range(5):
    a1, a2 = F.random_element(num_bound=5), F.random_element(num_bound=5)
    ft = Xr**2 * identity_matrix(RX, 3) + Xr * tilde(a1).change_ring(RX) \
        + tilde(a2).change_ring(RX)
    Nf = ft.det()
    check(Nf.degree() == 6 and Nf[5] == a1.trace() and Nf[0] == a2.norm(),
          '(9.10)(ii)')
    # Exercise 9.4: N f = prod over embeddings
    Fg = F.galois_closure('g')
    embs = F.embeddings(Fg)
    Yg = PolynomialRing(Fg, 'X').gen()
    pr = prod(Yg**2 + e(a1) * Yg + e(a2) for e in embs)
    check(pr == Nf.change_ring(Fg), 'Exercise 9.4')
    phi = matrix(F, 2, 2, [F.random_element(num_bound=4) for _ in range(4)])
    big = matrix.block([[tilde(phi[i, j]) for j in range(2)] for i in range(2)])
    cpL = phi.charpoly('X')
    cl = cpL.list()
    ftil = sum(tilde(cl[k]).change_ring(RX) * Xr**k for k in range(len(cl)))
    check(big.charpoly('X') == ftil.det(), '(9.10)(iii) (9.12)')

# (9.14)-(9.17): B = (-1, -1) over L = Q(2^(1/2)).
L2 = NumberField(X**2 - 2, 'r')
r = L2.gen()
BL = QuaternionAlgebra(L2, -1, -1)
QB = [r**k * b for b in BL.basis() for k in range(2)]


def qcoords(z):
    return [v for x in z.coefficient_tuple() for v in list(x)]


for _ in range(6):
    b = BL([L2.random_element(num_bound=4) for _ in range(4)])
    Lq = matrix(QQ, [qcoords(b * x) for x in QB]).transpose()
    rcl = b.reduced_characteristic_polynomial('X')
    cl = rcl.list()
    rtil = sum(matrix(QQ, [list(cl[k] * y) for y in [L2(1), r]]).transpose()
               .change_ring(RX) * Xr**k for k in range(len(cl)))
    red_BQ = rtil.det()
    check(Lq.charpoly('X') == red_BQ**2, '(9.16) char pol = (red)^m')
    check(-red_BQ[3] == b.reduced_trace().trace()
          and red_BQ[0] == b.reduced_norm().norm(), '(9.15)')
    check(Lq.trace() == 2 * b.reduced_trace().trace(), '(9.17)')

# Remark after (9.19): k[x, y]/(x, y)^2 is not Frobenius.
Pl = PolynomialRing(QQ, ['l1', 'lx', 'ly'])
l1, lx, ly = Pl.gens()
lam = {'1': l1, 'x': lx, 'y': ly}
prodtab = {('1', '1'): '1', ('1', 'x'): 'x', ('1', 'y'): 'y', ('x', '1'): 'x',
           ('y', '1'): 'y', ('x', 'x'): None, ('x', 'y'): None,
           ('y', 'x'): None, ('y', 'y'): None}
names = ['1', 'x', 'y']
Gram = matrix(Pl, 3, 3, lambda a, b: 0 if prodtab[names[a], names[b]] is None
              else lam[prodtab[names[a], names[b]]])
check(Gram.det() == 0, 'every associative form on k[x,y]/(x,y)^2 degenerate')
check(matrix(Pl, 3, 3, 0).is_symmetric(), 'the zero form: symmetric, assoc.')

# (9.31) for Q S_3 and Bourbaki's example.
S3 = SymmetricGroup(3)
els = list(S3)
for _ in range(4):
    coeffs = [randint(-3, 3) for _ in els]
    La = matrix(QQ, 6, 6, 0)
    Ra = matrix(QQ, 6, 6, 0)
    for col, h in enumerate(els):
        for cg, g in zip(coeffs, els):
            La[els.index(g * h), col] += cg
            Ra[els.index(h * g), col] += cg
    check(La.charpoly('X') == Ra.charpoly('X'), '(9.31) Q S_3')
# basis 1, x, y with x^2 = x, xy = y, yx = 0, y^2 = 0
tab = {(0, 0): [1, 0, 0], (0, 1): [0, 1, 0], (0, 2): [0, 0, 1],
       (1, 0): [0, 1, 0], (2, 0): [0, 0, 1], (1, 1): [0, 1, 0],
       (1, 2): [0, 0, 1], (2, 1): [0, 0, 0], (2, 2): [0, 0, 0]}


def bmul(a, b):
    out = vector(QQ, 3)
    for i in range(3):
        for j in range(3):
            out += a[i] * b[j] * vector(QQ, tab[i, j])
    return out


ebasis = [vector(QQ, v) for v in ([1, 0, 0], [0, 1, 0], [0, 0, 1])]
check(all(bmul(bmul(a, b), cc) == bmul(a, bmul(b, cc))
          for a in ebasis for b in ebasis for cc in ebasis),
      "Bourbaki's algebra is associative")
xv = ebasis[1]
xL = matrix(QQ, [bmul(xv, b) for b in ebasis]).transpose()
xR = matrix(QQ, [bmul(b, xv) for b in ebasis]).transpose()
check(xL == matrix(QQ, [[0, 0, 0], [1, 1, 0], [0, 0, 1]])
      and xR == matrix(QQ, [[0, 0, 0], [1, 1, 0], [0, 0, 0]]),
      'printed x_L, x_R (p. 124)')
check(xL.charpoly() != xR.charpoly() and xL.trace() == 2 and xR.trace() == 1,
      'different char pols and traces')
check((1 + xL).det() == 4 and (1 + xR).det() == 2, 'det (1+x)_L, (1+x)_R')

# Exercise 9.1.
Z5 = CyclotomicField(5)
z = Z5.gen()
reg = matrix(QQ, [list(z * z**k) for k in range(4)]).transpose()
a_mat = reg + reg.inverse()
mp = (z + z**(-1)).minpoly('X')
check(a_mat.charpoly('X') == mp**2, 'Exercise 9.1: (min pol)^(E : K(a))')

# Exercise 9.5 for M_2((-1, -1)_Q).


def hmat(q):
    c0, c1, c2, c3 = q.coefficient_tuple()
    al, be = c0 + c1 * I, c2 + c3 * I
    return matrix(Qi, [[al, be], [-be.conjugate(), al.conjugate()]])


for _ in range(5):
    M2 = [[H([randint(-3, 3) for _ in range(4)]) for _ in range(2)]
          for _ in range(2)]
    big = matrix.block([[hmat(M2[a][b]) for b in range(2)] for a in range(2)])
    check(big.trace() == M2[0][0].reduced_trace() + M2[1][1].reduced_trace(),
          'Exercise 9.5')

# --------------------------------------------------------------- Section 10
Lip = [H(1), qi, qj, qi * qj]
Hur = [(1 + qi + qj + qi * qj) / 2, qi, qj, qi * qj]


def disc(basis):
    return matrix(QQ, 4, 4, lambda a, b: (basis[a] * basis[b]).reduced_trace()
                  ).det()


check(abs(disc(Lip)) == 16 and abs(disc(Hur)) == 4, 'Exercise 10.2')
check(abs(disc(Lip)) == 2**2 * abs(disc(Hur)), 'Exercise 10.3: index^2')
Omax = H.maximal_order()
check(matrix(QQ, [list(b) for b in Omax.basis()]).row_module(ZZ)
      == matrix(QQ, [list(b) for b in Hur]).row_module(ZZ),
      'Exercise 10.2: Lambda_0 is the maximal order')
check(all((a * b).reduced_trace() in ZZ and (a * b).reduced_norm() in ZZ
          for a in Hur for b in Hur), '(10.1) integral tr, nr')
Ft = FunctionField(GF(2), 't')
t = Ft.gen()
for m in range(1, 13):
    check((1 / t)**m + (1 / t)**m == 0, 'Exercise 10.1: tr(a^m) = 0 in char 2')
check((1 / t) not in PolynomialRing(GF(2), 't'),
      'Exercise 10.1: a = (1/t, 1/t) is not integral over F_2[t]')

# Faddeev's example.
for n in [1, 2]:
    d = n + 1
    upper = [E(d, i, j) for i in range(d) for j in range(i, d)]
    Lam = lattice_rows(upper)
    rad = {k: [E(d, i, j) for i in range(d) for j in range(d) if j - i >= k]
           for k in range(1, n + 1)}
    rr = 2

    def Lam_k(k):
        gens = list(upper)
        for i in range(1, n + 1):
            gens += [QQ(rr)**(-i * k) * m for m in rad[i]]
        return lattice_rows(gens)
    prev = None
    for k in range(0, 6):
        Lk = Lam_k(k)
        B = [matrix(QQ, d, d, list(v)) for v in Lk.basis()]
        check(all(vector(QQ, (a * b).list()) in Lk for a in B for b in B)
              and vector(QQ, identity_matrix(QQ, d).list()) in Lk,
              "Faddeev: Lambda_k is an order")
        if prev is not None:
            check(prev.is_submodule(Lk) and prev != Lk,
                  'Faddeev: strictly increasing')
        prev = Lk
        scaled = lattice_rows([QQ(rr)**(n * (k + 1))
                               * matrix(QQ, d, d, list(v)) for v in Lk.basis()])
        target_n = lattice_rows([rr**n * m for m in upper])
        target_k = lattice_rows([rr**k * m for m in upper])
        check(scaled.is_submodule(target_n), 'corrected: L_n in r^n Lambda')
        if k > n:
            check(not scaled.is_submodule(target_k),
                  'printed r^k inference refuted')

# Proof of (10.8): Lambda = {(a, b) : a = b mod 2}.
Lam_pairs = lambda a, b: (a - b) % 2 == 0
kernel = [(a, b) for a in range(-6, 7) for b in range(-6, 7)
          if Lam_pairs(a, b) and b == 0]
check(all(a % 2 == 0 for a, b in kernel), "Lambda' = 2Z e_1")
check(not Lam_pairs(1, 0), 'e_1 not in Lambda')
# a splitting s(e_2) = j = (a, 1) in Lambda with Lambda' j = 0 forces a = 0
sols = [(a, 1) for a in range(-20, 21) if Lam_pairs(a, 1) and 2 * a == 0]
check(sols == [], 'no Lambda-splitting: (0, 1) is not in Lambda')

# --------------------------------------------------------------- Section 11
PS = PowerSeriesRing(QQ, 'y', default_prec=30)
yy = PS.gen()
sq = (1 + yy).sqrt()
check(sq**2 == 1 + yy and all(sq[k] == binomial(QQ(1) / 2, k)
                              for k in range(30)),
      '(11.5) counterexample: s = (1 + y)^(1/2) in Q[[y]]')
Qy = PolynomialRing(QQ, 'y').fraction_field()
check(not Qy(Qy.gen() + 1).is_square(), '1 + y is not a square in Q(y)')
Pxs = PolynomialRing(QQ, ['x', 's'])
Fxs = Pxs.fraction_field()
xx, ss = Fxs.gens()
Aq = QuaternionAlgebra(Fxs, xx, ss**2)
ii, jj, _ = Aq.gens()
kk = ii * jj
E11 = (1 + jj / ss) / 2
E22 = (1 - jj / ss) / 2
E21 = ii * E11
E12 = E11 * ii / xx
Eab = {(1, 1): E11, (1, 2): E12, (2, 1): E21, (2, 2): E22}
for (a, b), u in Eab.items():
    for (cc, dd), v in Eab.items():
        expected = Eab[a, dd] if b == cc else Aq(0)
        check(u * v == expected, '(11.5) matrix units')
check(E11 + E22 == 1, '(11.5) E_11 + E_22 = 1')
# coordinates of 1, i, j, ij in the E_ab
coords = {
    'one': {(1, 1): 1, (2, 2): 1},
    'i': {(2, 1): 1, (1, 2): xx},
    'j': {(1, 1): ss, (2, 2): -ss},
}
for name, elt in [('one', Aq(1)), ('i', ii), ('j', jj)]:
    check(sum(cf * Eab[k] for k, cf in coords[name].items()) == elt,
          '(11.5) Lambda^ inside M')
ij_coords = {k: 0 for k in Eab}
# ij = (E_21 + x E_12) s (E_11 - E_22) = s E_21 - s x E_12
check(ss * E21 - ss * xx * E12 == kk, '(11.5) ij in M')
# E_12 in the basis 1, i, j, ij of Lambda: coefficients 1/(2x), -1/(2xs)
check(E12 == ii / (2 * xx) - kk / (2 * xx * ss),
      '(11.5) E_12 = i/(2x) - ij/(2xs) is not in Lambda^')
basis_L = [Aq(1), ii, jj, kk]
dL = matrix(Fxs, 4, 4, lambda a, b: (basis_L[a] * basis_L[b]).reduced_trace()
            ).det()
check(dL == -16 * xx**2 * ss**4, '(11.5) d(R<i,j>) = -16 x^2 (1+y)^2')
basis_M = list(Eab.values())
dM = matrix(Fxs, 4, 4, lambda a, b: (basis_M[a] * basis_M[b]).reduced_trace()
            ).det()
check(dM == -1, '(11.5) d(M) = -1')
check(all((ii * w).reduced_trace() in [0, 2 * xx] for w in basis_L),
      '(11.5) tr(i Lambda) in x R')
check((ii / xx).reduced_norm() == -1 / xx, '(11.5) i/x not integral')

print(f'ok s08_11_orders: {N} checks')
