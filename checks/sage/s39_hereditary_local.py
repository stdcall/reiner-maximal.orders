"""Local hereditary orders: exact checks of Section 39 (pp. 352-366).

The local ring is modelled globally: for D = K = QQ the order Lambda of
(39.15) with invariants {n_1, ..., n_r} is the ZZ-order of all integer
n x n block matrices whose blocks above the diagonal have entries in pZ.
Its completion at p is the order (39.15) over Z_p, and its completions at
the other primes are maximal, so every equality below between ZZ-lattices
is equivalent to the corresponding equality over Z_p.  The radical is
J = Lambda cap rad Lambda_p, computed as the preimage of rad(Lambda/p Lambda)
by the characteristic-p algorithm of Friedl-Ronyai (integer matrices,
characteristic polynomials over ZZ reduced mod p).  For a quaternion
skewfield D (ramification index e = 2) the order Delta is a maximal order of
the definite quaternion algebra over QQ ramified at p, frak(p) its two-sided
prime over p.

Checked for every composition (n_1, ..., n_r) of n <= 4 (p = 2) and of
n <= 3 (p = 3) when D = QQ, and for the invariants (1), (2), (1, 1) (p = 2, 3)
and (1, 1, 1) (p = 2) when D is a quaternion skewfield:

* (39.14)(ii)-(iii), (39.16)-(39.17): Lambda is an order, its radical is
  the matrix (39.16), Lambda/J is semisimple with center of dimension
  r [K(Delta-bar) : F_p] and dimension sum n_i^2 [Delta-bar : F_p].
* (39.18), with the corrected (39.22): J^i M is the column lattice with
  frak(p) in the first n_1 + ... + n_i rows (refuted printed reading: n_1 +
  ... + n_(i-1) rows, which for i = 1 would give JM = M); J^r M = M frak(p)
  and r is the least such exponent; (39.19), (39.20) as stabilizers; J^(re)
  = p Lambda; J is invertible with inverse p^-1 J^(re-1) (Remark after
  (39.18)); O_l(J) = O_r(J) = Lambda ((39.11): Lambda extremal).
* (39.23): Gamma_t = End(J^t M), 0 <= t < r, are maximal (conjugates of
  M_n(Delta) by diagonal matrices), distinct, Gamma_r = Gamma_0, and their
  intersection is Lambda; p Gamma_t in Lambda.
* End of the proof of (39.14): for n_1 = ... = n_r = 1,
  rad Lambda_0 = Lambda_0 Pi (Pi as printed) and Pi^n = pi_D.
* Exercise 39.6 (p. 365), in part: for 0 < k < r the ideal J^k lies strictly
  between p Lambda and Lambda, so (J) has order exactly r = re in
  Picent Lambda (D = QQ).
* Exercise 39.7 (p. 365), D = QQ: enumerating all lattices between Lambda
  and each Gamma_t that are rings (Lambda-bimodules first),
  there are exactly 2^r - 1 orders containing Lambda, namely the
  intersections of the non-empty subsets of {Gamma_t}; a maximal chain
  Lambda < ... has r terms; the orders minimally containing Lambda are the
  r intersections of r - 1 of the Gamma_t when r >= 2 (none when r = 1).
* Exercise 39.9 (p. 365), D = QQ: J_t = {x in Lambda : x J^t M in J^(t+1)M}
  are r distinct maximal two-sided ideals, Lambda/J_t = M_(n_(t+1))(F_p),
  J = cap J_t and Lambda/J = sum Lambda/J_t (Chinese remainder theorem);
  rad Gamma_t = p Gamma_t is contained in J; the printed J_t = rad Gamma_t
  fails for every r >= 2, and J_t is then not an ideal of Gamma_t (so
  Gamma_t/J_t is not a ring): refuted printed readings.  The conductors are
  {x : Gamma_t x in Lambda} = {x : x J^(t+1) M in J^(t+r) M} and
  {x : x Gamma_t in Lambda} = {x : x J^t M in J^(t+r-1) M}.
* Exercises 39.10-39.11: J^r Gamma_t = rad Gamma_t for each t (D a
  quaternion skewfield; trivial for e = 1); for D = QQ and
  Lambda' = Gamma_0 the ideals L_i = J^i Lambda' J^-(i-1) give the proper
  product rad Lambda' = L_r ... L_1, and Lambda = cap O_l(L_i).
* Exercise 39.12: M_2(ZZ) cap diag(1, p^2) M_2(ZZ) diag(1, p^-2) is not
  hereditary at p: O_l(J) differs from it.
* Exercise 39.13: for D = QQ, p = 2, n = 4, the hereditary orders with
  invariants (1, 3) and (2, 2) (type 2) are the left and right orders of the
  lattice Y = {x : x E2_i in E1_i}.
* Lemma (39.10) and Exercise 39.5 over F_2, F_3: for every chain E of
  F_q^n (n = 2, q in {2, 3}; n = 3, q = 2) the radical of O(E) is (39.8);
  O(E) contains O(E') iff E' refines E; O(E) radically covers O(E') iff
  E = E'; and among all unital subalgebras of M_2(F_2), M_2(F_3), M_3(F_2)
  the extremal ones are exactly the chain rings.

Not established: the statements for other local rings or skewfields than
those listed; the global results of Section 40.
"""
from sage.all import (QQ, ZZ, GF, Integer, QuaternionAlgebra, identity_matrix,
                      matrix, vector, lcm, prod)
import itertools

N = 0


def ok(cond, msg=''):
    global N
    assert cond, msg
    N += 1


# --- lattice tools ----------------------------------------------------------------
def lat(rows):
    M = matrix(QQ, [list(r) for r in rows])
    den = M.denominator()
    H = (den * M).change_ring(ZZ).echelon_form(include_zero_rows=False)
    return H.change_ring(QQ) / den


def contains(big, small):
    return all(big.solve_left(v).denominator() == 1 for v in small.rows())


def same(a, b):
    return a.nrows() == b.nrows() and contains(a, b) and contains(b, a)


def lat_sum(a, b):
    return lat(list(a.rows()) + list(b.rows()))


def lat_cap(a, b):
    d = lcm(a.denominator(), b.denominator())
    M1 = (d * a).change_ring(ZZ).row_module()
    M2 = (d * b).change_ring(ZZ).row_module()
    return M1.intersection(M2).basis_matrix().change_ring(QQ) / d


def radical_mod_p(Ls, e, p):
    """rad(Lambda/p Lambda) (Friedl-Ronyai, integer matrices)."""
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


class Alg:
    """A matrix algebra M_n(B) over QQ (B = QQ or a quaternion algebra),
    elements as coordinate vectors."""

    def __init__(self, n, B=None):
        self.n, self.B = n, B
        self.k = 1 if B is None else 4
        self.dim = n * n * self.k
        self.basisB = [1] if B is None else [B(1)] + list(B.gens())

    def to(self, v):
        k, n = self.k, self.n
        if self.B is None:
            return matrix(QQ, n, n, list(v))
        return [[sum(v[(i * n + j) * k + c] * self.basisB[c] for c in range(k))
                 for j in range(n)] for i in range(n)]

    def fr(self, m):
        if self.B is None:
            return vector(QQ, m.list())
        return vector(QQ, [c for i in range(self.n) for j in range(self.n)
                           for c in list(m[i][j])])

    def mul(self, u, v):
        if self.B is None:
            return self.fr(self.to(u) * self.to(v))
        a, b = self.to(u), self.to(v)
        n = self.n
        return self.fr([[sum(a[i][l] * b[l][j] for l in range(n)) for j in range(n)]
                        for i in range(n)])

    def act(self, u, w):
        """u in M_n(B) acting on a column w in B^n (coordinates)."""
        if self.B is None:
            return self.to(u) * vector(QQ, list(w))
        a, n, k = self.to(u), self.n, self.k
        col = [sum(w[i * k + c] * self.basisB[c] for c in range(k)) for i in range(n)]
        return vector(QQ, [c for i in range(n)
                           for c in list(sum(a[i][l] * col[l] for l in range(n)))])

    def colact(self, w, d):
        """right multiplication of a column w by d in B."""
        if self.B is None:
            return vector(QQ, list(w)) * d
        n, k = self.n, self.k
        return vector(QQ, [c for i in range(n) for c in
                           list(sum(w[i * k + c] * self.basisB[c] for c in range(k)) * d)])

    def one(self):
        if self.B is None:
            return self.fr(identity_matrix(QQ, self.n))
        return self.fr([[self.B(1) if i == j else self.B(0) for j in range(self.n)]
                        for i in range(self.n)])

    def std(self):
        return [vector(QQ, [1 if a == b else 0 for b in range(self.dim)])
                for a in range(self.dim)]


def lat_mul(A, L1, L2):
    return lat([A.mul(u, v) for u in L1.rows() for v in L2.rows()])


def dual_solutions(A, conds, target):
    """{x in A : f(x) in target for f in conds}, each f linear A -> space of target."""
    Tinv = target.inverse()
    cols = []
    for f in conds:
        imgs = matrix(QQ, [f(e) for e in A.std()]) * Tinv
        cols += list(imgs.columns())
    W = lat(cols)
    ok(W.nrows() == A.dim)
    return lat((W.inverse()).transpose().rows())


def colon_mod(A, src, dst):
    """{x : x src in dst} for column lattices src, dst."""
    conds = [lambda x, w=w: A.act(x, w) for w in src.rows()]
    return dual_solutions(A, conds, dst)


def left_order(A, L):
    return dual_solutions(A, [lambda x, b=b: A.mul(x, b) for b in L.rows()], L)


def right_order(A, L):
    return dual_solutions(A, [lambda x, b=b: A.mul(b, x) for b in L.rows()], L)


def colon_right(A, G, L):
    """{x : G x in L}."""
    return dual_solutions(A, [lambda x, g=g: A.mul(g, x) for g in G.rows()], L)


def colon_left(A, G, L):
    """{x : x G in L}."""
    return dual_solutions(A, [lambda x, g=g: A.mul(x, g) for g in G.rows()], L)


def regular(A, L):
    Bm = L
    Ls = [matrix(QQ, [Bm.solve_left(A.mul(b, c)) for c in Bm.rows()]).transpose()
          for b in Bm.rows()]
    return [m.change_ring(ZZ) for m in Ls], Bm.solve_left(A.one())


def rad_p(A, L, p):
    Ls, e = regular(A, L)
    rad = radical_mod_p(Ls, e.change_ring(ZZ), p)
    return lat([p * r for r in L.rows()] + [vector(QQ, list(v)) * L for v in rad])


def center_dim_mod(A, L, I, p):
    """(dim of the center, dim) over F_p of L / I, I a two-sided ideal of the
    order L containing p L; computed in L-coordinates modulo p."""
    F = GF(p)
    m = L.nrows()
    Lc = lambda v: L.solve_left(v)
    Ibar = matrix(F, [[F(c) for c in Lc(v)] for v in I.rows()]).row_space()
    dI = Ibar.dimension()
    # x = sum a_i x_i is central mod I iff [x, x_k] in I for all k
    C = [vector(F, sum([[F(c) for c in Lc(A.mul(x, b) - A.mul(b, x))]
                        for b in L.rows()], [])) for x in L.rows()]
    G = []
    for k in range(m):
        for v in Ibar.basis():
            w = [F(0)] * (m * m)
            w[k * m:(k + 1) * m] = list(v)
            G.append(vector(F, w))
    K = matrix(F, C + G).left_kernel()
    Z = matrix(F, [list(k)[:m] for k in K.basis()] + [list(v) for v in Ibar.basis()]).row_space()
    return Z.dimension() - dI, m - dI


# --- the D = QQ case -------------------------------------------------------------
def compositions(n):
    for k in range(1, n + 1):
        for c in itertools.product(range(1, n + 1), repeat=k):
            if sum(c) == n:
                yield c


def block_index(comp):
    b = []
    for i, c in enumerate(comp):
        b += [i] * c
    return b


def monomial(A, expo, p):
    n = A.n
    return lat([p**expo[i][j] * A.fr(matrix(QQ, n, n, {(i, j): 1}))
                for i in range(n) for j in range(n)])


def column(A, ex, p):
    n = A.n
    return lat([p**ex[i] * vector(QQ, [1 if k == i else 0 for k in range(n)])
                for i in range(n)])


def subspaces(d, p):
    """All subspaces of F_p^d, as lists of integer row vectors (RREF)."""
    out = [[]]
    for k in range(1, d + 1):
        for piv in itertools.combinations(range(d), k):
            free = [(i, j) for i in range(k) for j in range(d)
                    if j > piv[i] and j not in piv]
            for vals in itertools.product(range(p), repeat=len(free)):
                rows = [[0] * d for _ in range(k)]
                for i in range(k):
                    rows[i][piv[i]] = 1
                for (i, j), v in zip(free, vals):
                    rows[i][j] = v
                out.append(rows)
    return out


def is_ring(A, L):
    return all(L.solve_left(A.mul(u, v)).denominator() == 1
               for u in L.rows() for v in L.rows())


for p in [2, 3]:
    for n in range(1, 5 if p == 2 else 4):
        A = Alg(n)
        for comp in compositions(n):
            r = len(comp)
            bl = block_index(comp)
            Lam = monomial(A, [[1 if bl[i] < bl[j] else 0 for j in range(n)]
                                for i in range(n)], p)
            ok(is_ring(A, Lam) and contains(Lam, lat([A.one()])))
            J = rad_p(A, Lam, p)
            Jf = monomial(A, [[1 if bl[i] <= bl[j] else 0 for j in range(n)]
                              for i in range(n)], p)
            ok(same(J, Jf), (p, comp))                              # (39.16)
            cd, dq = center_dim_mod(A, Lam, J, p)
            ok(cd == r and dq == sum(c * c for c in comp), (p, comp))  # (39.17)
            # chain J^i M, (39.22) corrected, and printed reading refuted
            M = column(A, [0] * n, p)
            Jpow = [lat([A.one()])]
            JM = [M]
            for i in range(1, r + 1):
                JM.append(lat([A.act(x, w) for x in J.rows() for w in JM[-1].rows()]))
            for i in range(r + 1):
                first = sum(comp[:i])
                ok(same(JM[i], column(A, [1 if k < first else 0 for k in range(n)], p)))
            if r >= 1:
                printed1 = column(A, [1 if k < 0 else 0 for k in range(n)], p)
                ok(not same(JM[1], printed1))                       # printed (n_(i-1)) refuted
            ok(same(JM[r], lat([p * w for w in M.rows()])))         # J^r M = M p
            ok(all(not same(JM[s], lat([p * w for w in M.rows()])) for s in range(r)))
            # (39.19), (39.20)
            S = colon_mod(A, JM[0], JM[0])
            for i in range(1, r + 1):
                S = lat_cap(S, colon_mod(A, JM[i], JM[i]))
            ok(same(S, Lam))
            Sj = colon_mod(A, JM[0], JM[1])
            for i in range(1, r):
                Sj = lat_cap(Sj, colon_mod(A, JM[i], JM[i + 1]))
            ok(same(Sj, J))
            # J^r = p Lambda, invertibility, extremality
            Jr = J
            Jpows = [Lam, J]
            for i in range(2, r + 1):
                Jpows.append(lat_mul(A, Jpows[-1], J))
            ok(same(Jpows[r], lat([p * x for x in Lam.rows()])))
            Jinv = lat([x / p for x in Jpows[r - 1].rows()])
            ok(same(lat_mul(A, J, Jinv), Lam) and same(lat_mul(A, Jinv, J), Lam))
            ok(same(left_order(A, J), Lam) and same(right_order(A, J), Lam))  # (39.11)
            # (39.23)
            Gam = []
            for t in range(r):
                first = sum(comp[:t])
                g = [1 if k < first else 0 for k in range(n)]
                Gt = colon_mod(A, JM[t], JM[t])
                Gf = monomial(A, [[g[i] - g[j] for j in range(n)] for i in range(n)], p)
                ok(same(Gt, Gf))                                   # conjugate of M_n(Z)
                ok(contains(Gt, Lam) and contains(Lam, lat([p * x for x in Gt.rows()])))
                Gam.append(Gt)
            ok(all(not same(Gam[s], Gam[t]) for s in range(r) for t in range(s)))
            ok(same(colon_mod(A, JM[r], JM[r]), Gam[0]))
            I = Gam[0]
            for t in range(1, r):
                I = lat_cap(I, Gam[t])
            ok(same(I, Lam))
            # Lambda_0 with all n_i = 1: rad = Lambda_0 Pi, Pi^n = p
            if all(c == 1 for c in comp):
                Pi = matrix(QQ, n, n, lambda i, j: 1 if i == j + 1 else (p if (i == 0 and j == n - 1) else 0))
                ok(same(lat([A.mul(x, A.fr(Pi)) for x in Lam.rows()]), J))
                ok(Pi**n == p * identity_matrix(QQ, n))
            # Exercise 39.9
            Jt = []
            for t in range(r):
                Jt.append(lat_cap(Lam, colon_mod(A, JM[t], JM[t + 1])))
            for t in range(r):
                ok(same(lat_mul(A, Lam, Jt[t]), Jt[t]) and same(lat_mul(A, Jt[t], Lam), Jt[t]))
                cd, dq = center_dim_mod(A, Lam, Jt[t], p)
                ok(cd == 1 and dq == comp[t]**2, (p, comp, t))      # Lambda/J_t = M_(n_(t+1))(F_p)
                radG = lat([p * x for x in Gam[t].rows()])
                ok(same(rad_p(A, Gam[t], p), radG))                # rad Gamma_t = p Gamma_t
                ok(contains(J, radG) and contains(Jt[t], J))
                if r >= 2:
                    ok(not same(Jt[t], radG))                      # printed J_t = rad Gamma_t refuted
                    ok(not same(lat_mul(A, Gam[t], Jt[t]), Jt[t])
                       or not same(lat_mul(A, Jt[t], Gam[t]), Jt[t]))  # not a Gamma_t-ideal
                # conductors
                # J^(t+r) M = p J^t M
                ok(same(colon_right(A, Gam[t], Lam),
                        colon_mod(A, JM[t + 1], lat([p * w for w in JM[t].rows()]))))
                ok(same(colon_left(A, Gam[t], Lam),
                        colon_mod(A, JM[t], lat([p * w for w in JM[t - 1].rows()])) if t >= 1
                        else colon_mod(A, JM[0], JM[r - 1])))
            ok(all(not same(Jt[s], Jt[t]) for s in range(r) for t in range(s)))
            I = Jt[0]
            for t in range(1, r):
                I = lat_cap(I, Jt[t])
            ok(same(I, J))
            for s in range(r):
                others = Lam
                for t in range(r):
                    if t != s:
                        others = lat_cap(others, Jt[t])
                ok(same(lat_sum(Jt[s], others), Lam))               # CRT
            # Exercise 39.11 (Exercise 39.10 is trivial for e = 1; see below)
            Lp = Gam[0]
            Ls_ = []
            Jneg = [Lam, Jinv]
            for i in range(2, r + 1):
                Jneg.append(lat_mul(A, Jneg[-1], Jinv))
            for i in range(1, r + 1):
                Ls_.append(lat_mul(A, lat_mul(A, Jpows[i], Lp), Jneg[i - 1]))
            prodL = Ls_[-1]
            for i in range(r - 2, -1, -1):
                prodL = lat_mul(A, prodL, Ls_[i])
            ok(same(prodL, lat([p * x for x in Lp.rows()])))       # rad Lambda' = L_r ... L_1
            for i in range(r - 1):
                ok(same(right_order(A, Ls_[i + 1]), left_order(A, Ls_[i])))   # proper product
            I = left_order(A, Ls_[0])
            for i in range(1, r):
                I = lat_cap(I, left_order(A, Ls_[i]))
            ok(same(I, Lam))
            # Exercise 39.6 (part): J^k for 0 < k < r is not p^a Lambda
            for k in range(1, r):
                ok(not same(Jpows[k], Lam) and
                   not same(Jpows[k], lat([p * x for x in Lam.rows()])))
            # Exercise 39.7: orders between Lambda and Gamma_t.  Gamma_t / Lambda
            # has the F_p-basis of the monomials p^g_ij E_ij with lambda_ij =
            # g_ij + 1; an order is a Lambda-bimodule, so first the subspaces
            # invariant under left and right multiplication by Lambda, then
            # the ring condition on the lattices.
            if (p == 2 and n <= 4) or (p == 3 and n <= 3):
                lamx = [[1 if bl[i] < bl[j] else 0 for j in range(n)] for i in range(n)]
                orders = []
                for t in range(r):
                    first = sum(comp[:t])
                    g = [1 if k < first else 0 for k in range(n)]
                    gam = [[g[i] - g[j] for j in range(n)] for i in range(n)]
                    pos = [(i, j) for i in range(n) for j in range(n)
                           if lamx[i][j] == gam[i][j] + 1]
                    d = len(pos)
                    W = [matrix(QQ, n, n, {(i, j): p**gam[i][j]}) for (i, j) in pos]

                    def vcoords(x):
                        return [ZZ(x[i, j] / p**gam[i][j]) % p for (i, j) in pos]
                    gensL = [A.to(v) for v in Lam.rows()]
                    maps = []
                    for lam_ in gensL:
                        maps.append([vcoords(lam_ * w) for w in W])
                        maps.append([vcoords(w * lam_) for w in W])

                    def invariant(sub):
                        span = {tuple([0] * d)}
                        for row in sub:
                            span = {tuple((a + c * b) % p for a, b in zip(v, row))
                                    for v in span for c in range(p)}
                        for mp in maps:
                            for row in sub:
                                img = [sum(row[k] * mp[k][l] for k in range(d)) % p
                                       for l in range(d)]
                                if tuple(img) not in span:
                                    return False
                        return True
                    for sub in subspaces(d, p):
                        if not invariant(sub):
                            continue
                        L = lat(list(Lam.rows()) +
                                [A.fr(sum(c * w for c, w in zip(row, W))) for row in sub])
                        if is_ring(A, L) and not any(same(L, O) for O in orders):
                            orders.append(L)
                inters = []
                for k in range(1, r + 1):
                    for Ssub in itertools.combinations(range(r), k):
                        I = Gam[Ssub[0]]
                        for t in Ssub[1:]:
                            I = lat_cap(I, Gam[t])
                        inters.append((Ssub, I))
                ok(len(orders) == 2**r - 1, (p, comp, len(orders)))
                ok(all(any(same(O, I) for _, I in inters) for O in orders))
                ok(all(not same(I1, I2) for a1, I1 in inters for a2, I2 in inters
                       if a1 < a2))
                minimal = [O for O in orders if not same(O, Lam) and
                           not any(not same(O2, Lam) and not same(O2, O) and contains(O, O2)
                                   for O2 in orders)]
                ok(len(minimal) == (r if r >= 2 else 0), (p, comp))
                # longest chain Lambda = O_0 < ... : r orders
                longest = {}
                for O in sorted(orders, key=lambda L: abs(L.det())):
                    longest[id(O)] = 1 + max([longest[id(O2)] for O2 in orders
                                              if id(O2) in longest and not same(O2, O)
                                              and contains(O2, O)] + [0])
                ok(max(longest.values()) == r, (p, comp))

# Exercise 39.12
for p in [2, 3]:
    A = Alg(2)
    Lam = monomial(A, [[0, 0], [2, 0]], p)          # M_2(Z) cap diag(1,p^2) M_2(Z) diag(1,p^-2)
    J = rad_p(A, Lam, p)
    ok(not same(left_order(A, J), Lam))
# Exercise 39.13
A = Alg(4)
p = 2
E1 = [column(A, [1 if k < c else 0 for k in range(4)], p) for c in [0, 1]]
E2 = [column(A, [1 if k < c else 0 for k in range(4)], p) for c in [0, 2]]
b1, b2 = [0, 1, 1, 1], [0, 0, 1, 1]
L1 = monomial(A, [[1 if b1[i] < b1[j] else 0 for j in range(4)] for i in range(4)], p)
L2 = monomial(A, [[1 if b2[i] < b2[j] else 0 for j in range(4)] for i in range(4)], p)
Y = lat_cap(colon_mod(A, E2[0], E1[0]), colon_mod(A, E2[1], E1[1]))
ok(same(left_order(A, Y), L1) and same(right_order(A, Y), L2))


# --- D a quaternion skewfield (e = 2) ---------------------------------------------
def two_sided_prime(basis, p):
    gram = matrix(ZZ, [[(x * y).reduced_trace() for y in basis] for x in basis])
    ker = gram.change_ring(GF(p)).right_kernel().basis()
    return [p * x for x in basis] + [sum(ZZ(c) * b for c, b in zip(v, basis)) for v in ker]


for p in [2, 3]:
    Bq = QuaternionAlgebra(p)
    O = Bq.maximal_order()
    Ob = list(O.basis())
    Pgens = two_sided_prime(Ob, p)
    # a prime element pi_D in P with nr = p
    piD = None
    for c in itertools.product(range(-2, 3), repeat=4):
        x = sum(ci * b for ci, b in zip(c, Ob))
        if x.reduced_norm() == p:
            piD = x
            break
    ok(piD is not None)
    for comp in [(1,), (2,), (1, 1)] + ([(1, 1, 1)] if p == 2 else []):
        n = sum(comp)
        r = len(comp)
        A = Alg(n, Bq)
        bl = block_index(comp)

        def entry_lattice(rule):
            rows = []
            for i in range(n):
                for j in range(n):
                    for x in (Pgens if rule(i, j) else Ob):
                        m = [[Bq(0)] * n for _ in range(n)]
                        m[i][j] = x
                        rows.append(A.fr(m))
            return lat(rows)
        Lam = entry_lattice(lambda i, j: bl[i] < bl[j])
        ok(is_ring(A, Lam))
        J = rad_p(A, Lam, p)
        ok(same(J, entry_lattice(lambda i, j: bl[i] <= bl[j])), (p, comp))   # (39.16)
        cd, dq = center_dim_mod(A, Lam, J, p)
        ok(cd == 2 * r and dq == 2 * sum(c * c for c in comp), (p, comp))      # Delta-bar = F_(p^2)
        Jp = [Lam, J]
        for i in range(2, 2 * r + 1):
            Jp.append(lat_mul(A, Jp[-1], J))
        ok(same(Jp[2 * r], lat([p * x for x in Lam.rows()])))                  # J^(re) = p Lambda
        ok(not same(Jp[r], lat([p * x for x in Lam.rows()])))
        # J^r M = M pi_D for M = Delta^(n x 1)
        Mrows = []
        for i in range(n):
            for x in Ob:
                col = [Bq(0)] * n
                col[i] = x
                Mrows.append(vector(QQ, [c for y in col for c in list(y)]))
        M = lat(Mrows)
        JM = M
        for i in range(r):
            JM = lat([A.act(x, w) for x in J.rows() for w in JM.rows()])
        ok(same(JM, lat([A.colact(w, piD) for w in M.rows()])))
        ok(same(left_order(A, J), Lam))
        # (39.23)
        chain = [M]
        for i in range(r):
            chain.append(lat([A.act(x, w) for x in J.rows() for w in chain[-1].rows()]))
        Gam = [colon_mod(A, chain[t], chain[t]) for t in range(r)]
        I = Gam[0]
        for t in range(1, r):
            I = lat_cap(I, Gam[t])
        ok(same(I, Lam))
        ok(all(not same(Gam[s], Gam[t]) for s in range(r) for t in range(s)))
        # Exercise 39.10: J^r Gamma_t = rad Gamma_t
        for t in range(r):
            ok(same(lat_mul(A, Jp[r], Gam[t]), rad_p(A, Gam[t], p)))
        if all(c == 1 for c in comp) and n >= 1:
            Pi = [[Bq(1) if i == j + 1 else (piD if (i == 0 and j == n - 1) else Bq(0))
                   for j in range(n)] for i in range(n)]
            ok(same(lat([A.mul(x, A.fr(Pi)) for x in Lam.rows()]), J))      # rad Lambda_0 = Lambda_0 Pi


# --- Lemma (39.10), Exercise 39.5: chain rings over finite fields ------------------
def finite_part(n, p):
    elems = [tuple(m) for m in itertools.product(range(p), repeat=n * n)]
    idx = {m: i for i, m in enumerate(elems)}

    def mmul(a, b):
        return tuple(sum(a[i * n + l] * b[l * n + j] for l in range(n)) % p
                     for i in range(n) for j in range(n))
    table = [[idx[mmul(a, b)] for b in elems] for a in elems]
    addt = [[idx[tuple((x + y) % p for x, y in zip(a, b))] for b in elems] for a in elems]
    smul = [[idx[tuple((c * x) % p for x in a)] for a in elems] for c in range(p)]
    zero = idx[tuple([0] * (n * n))]
    one = idx[tuple(1 if i == j else 0 for i in range(n) for j in range(n))]

    def add_to_span(S, v):
        if v in S:
            return S
        return frozenset(addt[s][smul[c][v]] for s in S for c in range(p))

    def closure(S, basis, extra):
        basis = list(basis) + [extra]
        S = add_to_span(S, extra)
        changed = True
        while changed:
            changed = False
            for a in list(basis):
                for b in list(basis):
                    c = table[a][b]
                    if c not in S:
                        basis.append(c)
                        S = add_to_span(S, c)
                        changed = True
        return S, basis

    def vecs(n_):
        return [tuple(v) for v in itertools.product(range(p), repeat=n_)]

    def apply(a, v):
        m = elems[a]
        return tuple(sum(m[i * n + j] * v[j] for j in range(n)) % p for i in range(n))
    # subspaces of F_p^n and chains
    V = vecs(n)
    subs = set()
    for k in range(n + 1):
        for gens in itertools.combinations(V, k):
            S = {tuple([0] * n)}
            for g in gens:
                S = {tuple((x + c * y) % p for x, y in zip(s_, g)) for s_ in S for c in range(p)}
            subs.add(frozenset(S))
    full = frozenset(V)
    zv = frozenset([tuple([0] * n)])
    chains = []

    def rec(ch):
        if ch[-1] == zv:
            chains.append(tuple(ch))
            return
        for t in subs:
            if t < ch[-1]:
                rec(ch + [t])
    rec([full])
    ring = {E: frozenset(a for a in range(len(elems))
                         if all(apply(a, v) in W for W in E for v in W)) for E in chains}
    radf = {E: frozenset(a for a in ring[E]
                         if all(apply(a, v) in E[i + 1] for i in range(len(E) - 1) for v in E[i]))
            for E in chains}

    def radical(S):
        # basis of S over F_p, structure constants lifted to ZZ
        basis = []
        span = frozenset([zero])
        for a in sorted(S):
            if a not in span:
                basis.append(a)
                span = add_to_span(span, a)
        d = len(basis)
        coords = {}
        for cs in itertools.product(range(p), repeat=d):
            x = zero
            for c, b in zip(cs, basis):
                x = addt[x][smul[c][b]]
            coords[x] = cs
        Ls = [matrix(ZZ, [list(coords[table[b][c]]) for c in basis]).transpose()
              for b in basis]
        e = vector(ZZ, list(coords[one]))
        rad = radical_mod_p(Ls, e, p)
        R = frozenset([zero])
        for v in rad:
            x = zero
            for c, b in zip(v, basis):
                x = addt[x][smul[int(c) % p][b]]
            R = add_to_span(R, x)
        return R
    for E in chains:
        ok(radical(ring[E]) == radf[E], (n, p))                    # (39.8)
    for E in chains:
        for E2 in chains:
            ok((ring[E] >= ring[E2]) == (set(E) <= set(E2)))       # Exercise 39.5(i)
            ok((ring[E] >= ring[E2] and radf[E] >= radf[E2]) == (E == E2))  # (ii)
    start, b0 = closure(frozenset([zero]), [], one)
    seen = {start: b0}
    frontier = [start]
    while frontier:
        nxt = []
        for S in frontier:
            for m in range(len(elems)):
                if m not in S:
                    T, bT = closure(S, seen[S], m)
                    if T not in seen:
                        seen[T] = bT
                        nxt.append(T)
        frontier = nxt
    rads = {S: radical(S) for S in seen}
    chainset = set(ring.values())
    ok(chainset <= set(seen))
    for S in list(seen):
        extremal = not any(T != S and T >= S and rads[T] >= rads[S] for T in seen)
        ok(extremal == (S in chainset), (n, p))                    # Lemma (39.10)
    return len(seen), len(chainset)


for (n, p) in [(2, 2), (2, 3), (3, 2)]:
    finite_part(n, p)

print(f'ok s39_hereditary_local: {N} checks')
