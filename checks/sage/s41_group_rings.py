"""Integral group rings: exact checks of Section 41.

* (41.2) (pp. 379-380): in the regular representation of G, T(x) = |G| for x = 1
  and 0 for x != 1; all groups of order <= 32 (GAP).
* (41.1), (41.3)-(41.5) (pp. 379-382), Jacobinski's conductor formula, for
  G = C_2, C_3, C_4, C_5, C_6, C_8, C_2 x C_2, S_3, D_8 (order 8), Q_8: QQ G
  is mapped isomorphically onto a product of components (cyclotomic fields
  QQ(zeta_d), M_2(QQ), the quaternions (-1, -1)_QQ) by explicit irreducible
  rational representations; Gamma is the product of the maximal orders
  ZZ[zeta_d], M_2(ZZ), the order of Section 26 (cited in Remark (37.41)).
  Checked: Lambda = ZZ G is contained in Gamma, Gamma in n^-1 Lambda (41.1);
  the dual of Lambda for T is n^-1 Lambda (41.5); both conductors
  {x : x Gamma in Lambda} and {x : Gamma x in Lambda} equal
  n * dual(Gamma) and sum (n / n_i) D_i^-1, the inverse differents being
  computed for the reduced traces of the components (41.3); in particular
  Lambda is not hereditary: it is not maximal and Gamma != Lambda.
* Exercise 41.2 (p. 384): the conductor {x in ZZ : x Gamma in Lambda} equals
  the intersection of the ideals (n / n_i)(QQ cap D^-1(R_i / ZZ)), and
  R_i cap (n / n_i) D_i^-1 = (n / n_i) D^-1(R_i / ZZ), for these groups.
* Schilling's Theorem (41.9) (p. 383): for every group of order p^k with
  p^k in {3, ..., 3^5, 5, 25, 125, 7, 49} and every 2-group of order <= 32,
  and each irreducible character chi, the integer
  g(chi) = gcd <chi, Ind_H^G sum_sigma lambda^sigma> over all subgroups H
  and linear characters lambda of H (sigma over Gal(QQ(chi, lambda)/QQ(chi)))
  is a multiple of the Schur index m_QQ(chi) (Isaacs, Character Theory of
  Finite Groups, Cor. 10.2(c): an F-character has multiplicities divisible
  by m_F); g(chi) = 1 for p odd, and g(chi) in {1, 2} for p = 2, with
  g(chi) = 2 exactly when the Frobenius-Schur indicator is -1 (then
  m_RR(chi) = 2 divides m_QQ(chi)).  Hence m_QQ(chi) = 1 for odd p and
  m_QQ(chi) <= 2 for p = 2 on these groups.
* Exercise 41.1 (p. 384): n_i = chi(1) divides |G| for every irreducible
  character of every group of order <= 64.

Not established: Schilling's theorem for other groups; the conductor
formula for other groups.
"""
from sage.all import (QQ, ZZ, CyclotomicField, QuaternionAlgebra, gcd, lcm,
                      libgap, matrix, vector, zero_matrix, identity_matrix)
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


# --- (41.2) ---------------------------------------------------------------------
traces = libgap.eval('''
function()
  local n, i, G, els, x, ok;
  ok := true;
  for n in [1..32] do for i in [1..NrSmallGroups(n)] do
    G := SmallGroup(n, i); els := AsList(G);
    for x in els do
      if Trace(PermutationMat(Permutation(x, els, OnLeftInverse), n)) <>
         (function() if x = One(G) then return n; else return 0; fi; end)() then
        ok := false;
      fi;
    od;
  od; od;
  return ok;
end''')()
ok(bool(traces))

# --- components -----------------------------------------------------------------
class Field:
    def __init__(self, d):
        self.K = CyclotomicField(d, 'z%d' % d)
        self.dim = self.K.degree()
        self.ni = 1

    def el(self, v):
        return self.K(list(v))

    def vec(self, x):
        return vector(QQ, list(self.K(x)))

    def mul(self, u, v):
        return self.vec(self.el(u) * self.el(v))

    def trd(self, u):
        return self.el(u).trace()

    def maxorder(self):
        return lat([self.vec(b) for b in self.K.ring_of_integers().basis()])

    def one(self):
        return self.vec(1)


class Mat2:
    dim = 4
    ni = 2

    def el(self, v):
        return matrix(QQ, 2, 2, list(v))

    def vec(self, x):
        return vector(QQ, x.list())

    def mul(self, u, v):
        return self.vec(self.el(u) * self.el(v))

    def trd(self, u):
        return self.el(u).trace()

    def maxorder(self):
        return lat([vector(QQ, [1 if k == i else 0 for k in range(4)]) for i in range(4)])

    def one(self):
        return vector(QQ, [1, 0, 0, 1])


class Hamilton:
    dim = 4
    ni = 2

    def __init__(self):
        self.H = QuaternionAlgebra(QQ, -1, -1)

    def el(self, v):
        return self.H(list(v))

    def vec(self, x):
        return vector(QQ, list(x))

    def mul(self, u, v):
        return self.vec(self.el(u) * self.el(v))

    def trd(self, u):
        return self.el(u).reduced_trace()

    def maxorder(self):
        i, j, k = self.H.gens()
        return lat([self.vec(x) for x in [self.H(1), i, j, (1 + i + j + k) / 2]])

    def one(self):
        return self.vec(self.H(1))


def zcomp(comps, idx, v):
    out = []
    for c, comp in enumerate(comps):
        out += list(v) if c == idx else [0] * comp.dim
    return vector(QQ, out)


def split(comps, v):
    parts, k = [], 0
    for comp in comps:
        parts.append(v[k:k + comp.dim])
        k += comp.dim
    return parts


def pmul(comps, u, v):
    out = []
    for comp, a, b in zip(comps, split(comps, u), split(comps, v)):
        out += list(comp.mul(a, b))
    return vector(QQ, out)


def dual_solutions(dim, conds, target):
    cols = []
    std = [vector(QQ, [1 if a == b else 0 for b in range(dim)]) for a in range(dim)]
    for f in conds:
        cols += list(matrix(QQ, [target.solve_left(f(e)) for e in std]).columns())
    W = lat(cols)
    ok(W.nrows() == dim)
    return lat(W.inverse().transpose().rows())


def check_group(name, gens_images, comps, elements, n):
    """elements: list of tuples of component elements (images of all g in G)."""
    dim = sum(c.dim for c in comps)
    ok(dim == n, name)
    imgs = [vector(QQ, sum([list(c.vec(x)) for c, x in zip(comps, e)], []))
            for e in elements]
    Phi = matrix(QQ, imgs)
    ok(Phi.det() != 0, name)                               # QQ G = product of components
    Lam = lat(imgs)
    Gam = lat(sum([[zcomp(comps, i, v) for v in c.maxorder().rows()]
                   for i, c in enumerate(comps)], []))
    ok(contains(Gam, Lam) and contains(lat([v / n for v in Lam.rows()]), Gam), name)  # (41.1)
    ok(not same(Gam, Lam) or n == 1)
    # T = sum n_i tr_i; dual of Lambda is n^-1 Lambda (41.5)
    def T(v):
        return sum(c.ni * c.trd(p_) for c, p_ in zip(comps, split(comps, v)))
    def tdual(L):
        G = matrix(QQ, [[T(pmul(comps, u, w)) for w in L.rows()] for u in L.rows()])
        return lat(G.inverse() * L)
    ok(same(tdual(Lam), lat([v / n for v in Lam.rows()])), name)
    lc = dual_solutions(dim, [lambda x, g=g: pmul(comps, x, g) for g in Gam.rows()], Lam)
    rc = dual_solutions(dim, [lambda x, g=g: pmul(comps, g, x) for g in Gam.rows()], Lam)
    ok(same(lc, rc), name)                                  # (41.3), left = right
    ok(same(rc, lat([n * v for v in tdual(Gam).rows()])), name)
    # sum (n/n_i) D_i^-1, D_i^-1 for the reduced trace tr_i of A_i over QQ
    pieces = []
    for i, c in enumerate(comps):
        Oi = c.maxorder()
        G = matrix(QQ, [[c.trd(c.mul(u, w)) for w in Oi.rows()] for u in Oi.rows()])
        Dinv = lat(G.inverse() * Oi)
        pieces += [zcomp(comps, i, QQ(n) / c.ni * v) for v in Dinv.rows()]
        # Exercise 41.2, first assertion: R_i cap (n/n_i) D_i^-1 = (n/n_i) D^-1(R_i/ZZ)
        sc = lat([QQ(n) / c.ni * v for v in Dinv.rows()])
        if isinstance(c, Field):
            # Gamma_i = R_i: the assertion says (n/n_i) D_i^-1 lies in R_i
            ok(contains(Oi, sc), name)
        else:
            # center QQ, R_i = ZZ, D(R_i/ZZ) = ZZ: {t : t 1 in sc} = (n/n_i) ZZ
            cvec = sc.solve_left(c.one())
            ok(1 / gcd(list(cvec)) == QQ(n) / c.ni, name)
    cond = lat(pieces)
    ok(same(rc, cond), name)
    # Exercise 41.2: x in ZZ with x Gamma in Lambda
    m = 1
    while not contains(Lam, lat([m * v for v in Gam.rows()])):
        m += 1
    formula = 1
    for c in comps:
        if isinstance(c, Field):
            K = c.K
            Dinv = K.different()**-1
            # QQ cap D^-1: smallest positive rational in it, as a fraction
            q = min(QQ(1) / k for k in range(1, 9) if K(QQ(1) / k) in Dinv)
            term = QQ(n) * q
        else:
            term = QQ(n) / c.ni
        formula = lcm(formula, term)
    ok(m == formula, (name, m, formula))


def cyclic_components(nn):
    from sage.all import divisors
    return [Field(d) for d in divisors(nn)]


# C_n, C_2 x C_2
for nn in [2, 3, 4, 5, 6, 8]:
    comps = cyclic_components(nn)
    from sage.all import divisors
    elements = [tuple(c.K.zeta(d)**k for c, d in zip(comps, divisors(nn)))
                for k in range(nn)]
    check_group('C%d' % nn, None, comps, elements, nn)

comps = [Field(1) for _ in range(4)]
elements = []
for a in range(2):
    for b in range(2):
        elements.append(tuple(Field(1).K(s) for s in [1, (-1)**a, (-1)**b, (-1)**(a + b)]))
check_group('C2xC2', None, comps, elements, 4)

# S_3: trivial, sign, the 2-dimensional representation on the root lattice
F1 = Field(1)
M2 = Mat2()
r = matrix(QQ, [[0, -1], [1, -1]])     # order 3
s = matrix(QQ, [[0, 1], [1, 0]])       # a reflection
els = []
for k in range(3):
    for e in range(2):
        g = r**k * s**e
        els.append((F1.K(1), F1.K((-1)**e), g))
comps = [F1, Field(1), M2]
check_group('S3', None, comps, els, 6)

# D_8: four linear characters and the 2-dimensional representation
r = matrix(QQ, [[0, -1], [1, 0]])
s = matrix(QQ, [[1, 0], [0, -1]])
els = []
for k in range(4):
    for e in range(2):
        g = r**k * s**e
        els.append((F1.K(1), F1.K((-1)**k), F1.K((-1)**e), F1.K((-1)**(k + e)), g))
comps = [Field(1), Field(1), Field(1), Field(1), M2]
check_group('D8', None, comps, els, 8)

# Q_8: four linear characters and the quaternions
Hm = Hamilton()
i, j, k = Hm.H.gens()
els = []
for a in range(4):
    for b in range(2):
        g = i**a * j**b
        els.append((F1.K(1), F1.K((-1)**a), F1.K((-1)**b), F1.K((-1)**(a + b)), g))
comps = [Field(1), Field(1), Field(1), Field(1), Hm]
check_group('Q8', None, comps, els, 8)

# --- Schilling (41.9) ---------------------------------------------------------------
gfun = libgap.eval('''
function(G)
  local irr, out, chi, cv, g, H, res, lam, vals, N, ks, orbit, sum, inds,
        subs, lins, k;
  irr := Irr(G);
  inds := Indicator(CharacterTable(G), 2);
  subs := List(ConjugacyClassesSubgroups(G), Representative);
  lins := List(subs, H -> List(Filtered(Irr(H), l -> l[1] = 1),
                                ValuesOfClassFunction));
  out := [];
  for k in [1..Length(irr)] do
    chi := irr[k];
    cv := ValuesOfClassFunction(chi);
    g := 0;
    for H in [1..Length(subs)] do
      res := Restricted(chi, subs[H]);
      for vals in lins[H] do
        N := Conductor(Concatenation(cv, vals));
        # Gal(QQ(chi, lam)/QQ(chi)): residues mod N fixing the values of chi
        ks := Filtered(PrimeResidues(N), k -> GaloisCyc(cv, k) = cv);
        orbit := Set(ks, k -> GaloisCyc(vals, k));
        sum := Sum(orbit, v -> ClassFunction(subs[H], v));
        # <chi, Ind sum> = <chi|_H, sum> (Frobenius reciprocity)
        g := Gcd(g, ScalarProduct(res, sum));
        if g = 1 then break; fi;
      od;
      if g = 1 then break; fi;
    od;
    Add(out, [g, inds[k]]);
  od;
  return out;
end''')
counted = 0
for (p, maxk) in [(3, 5), (5, 3), (7, 2), (2, 5)]:
    for k in range(1, maxk + 1):
        for idx in range(1, int(libgap.NrSmallGroups(p**k)) + 1):
            G = libgap.SmallGroup(p**k, idx)
            for g, nu in gfun(G).sage():
                counted += 1
                if p != 2:
                    ok(g == 1, (p, k, idx))
                else:
                    ok(g in (1, 2) and ((g == 2) == (nu == -1)), (p, k, idx, g, nu))
ok(counted > 500)

# --- Exercise 41.1 -------------------------------------------------------------------
res = libgap.eval('''
ForAll([1..64], n -> ForAll([1..NrSmallGroups(n)], i ->
  ForAll(Irr(SmallGroup(n, i)), chi -> n mod chi[1] = 0)))''')
ok(bool(res))

print(f'ok s41_group_rings: {N} checks')
