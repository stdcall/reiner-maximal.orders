"""Finite subgroups of u(H) and Kaplansky's theorem (Section 38).

* Remark after (38.1) (pp. 343-344): a finite nonabelian group embeds in
  u(H) iff it has a faithful irreducible complex character of degree 2 with
  Frobenius-Schur indicator -1 (then it has exactly one involution).  GAP,
  over all nonabelian groups of order <= 120 with a unique involution: the
  groups with such a character are exactly the generalized quaternion
  (dicyclic) groups of order 4n, 2 <= n <= 30, and the binary tetrahedral,
  octahedral and icosahedral groups, identified with Coxeter's
  <2, 3, 3>, <2, 3, 4>, <2, 3, 5> (orders 24, 48, 120) and <2, 2, n> = Q_4n
  from the presentations <R, S, T | R^l = S^m = T^n = RST>.
* The deduction (ii) of that remark: for every group G of order <= 32, every
  irreducible character chi of degree 2 with indicator -1 (these give the
  totally definite quaternion components of QQ G: real field of values,
  local index 2 at every real prime) has G / ker chi in the list above.
* Kaplansky (38.13)(i) (pp. 347-348) on R = ZZ[sqrt -5]: for the isomorphism
  mu : a + a -> R + R, mu = (x^-1)^T with R^2 x = a + a, the entries satisfy
  alpha_ij M_j in N_i and N_1 N_2 = (det mu) M_1 M_2.

Not established: Coxeter's classification itself beyond order 120.
"""
from sage.all import QQ, QuadraticField, libgap, matrix
import itertools

N = 0


def ok(cond, msg=''):
    global N
    assert cond, msg
    N += 1


quat_test = libgap.eval('''
function(G)
  local T, irr, ind, k;
  T := CharacterTable(G);
  irr := Irr(T);
  ind := Indicator(T, 2);
  for k in [1..Length(irr)] do
    if irr[k][1] = 2 and ind[k] = -1 and Size(KernelOfCharacter(irr[k])) = 1 then
      return true;
    fi;
  od;
  return false;
end
''')
found = libgap.eval('''
function(QuatTest) return Filtered(Concatenation(List([1..120], n -> List([1..NrSmallGroups(n)], i -> [n, i]))),
  function(id)
    local G;
    G := SmallGroup(id[1], id[2]);
    if IsAbelian(G) then return false; fi;
    if Number(Elements(G), x -> Order(x) = 2) <> 1 then return false; fi;
    return QuatTest(G);
  end); end
''')(quat_test).sage()
found = sorted(tuple(x) for x in found)


def binary_polyhedral(l, m, n):
    G = libgap.eval('''
    function(l, m, n)
      local F, R, S, T;
      F := FreeGroup("R", "S", "T");
      R := F.1; S := F.2; T := F.3;
      return F / [R^l / (R*S*T), S^m / (R*S*T), T^n / (R*S*T)];
    end''')(l, m, n)
    return tuple(libgap.IdGroup(G).sage())


expected = set()
for n in range(2, 31):
    q = tuple(libgap.IdGroup(libgap.DicyclicGroup(4 * n)).sage())
    ok(q == binary_polyhedral(2, 2, n), n)          # <2, 2, n> = Q_4n
    expected.add(q)
bt, bo, bi = binary_polyhedral(2, 3, 3), binary_polyhedral(2, 3, 4), binary_polyhedral(2, 3, 5)
ok(bt == (24, 3) and bo == (48, 28) and bi == (120, 5))
ok(tuple(libgap.IdGroup(libgap.SL(2, 3)).sage()) == bt)
ok(tuple(libgap.IdGroup(libgap.SL(2, 5)).sage()) == bi)
expected |= {bt, bo, bi}
ok(set(found) == expected, (set(found) ^ expected))

# deduction (ii): totally definite quaternion components of QQ G
quots = libgap.eval('''
Concatenation(List([1..32], n -> Concatenation(List([1..NrSmallGroups(n)], function(i)
  local G, T, irr, ind, k, out;
  G := SmallGroup(n, i); T := CharacterTable(G); irr := Irr(T);
  ind := Indicator(T, 2); out := [];
  for k in [1..Length(irr)] do
    if irr[k][1] = 2 and ind[k] = -1 then
      Add(out, IdGroup(G / KernelOfCharacter(irr[k])));
    fi;
  od;
  return out;
end))))''').sage()
ok(len(quots) > 0)
for q in quots:
    ok(tuple(q) in expected, q)

# --- Kaplansky (38.13)(i) on ZZ[sqrt -5] ----------------------------------------
K = QuadraticField(-5, 's')
s = K.gen()
a = K.ideal(2, 1 + s)
ab = a.basis()
x = None
for cs in itertools.product(range(-2, 3), repeat=8):
    v1 = [cs[0] * ab[0] + cs[1] * ab[1], cs[2] * ab[0] + cs[3] * ab[1]]
    v2 = [cs[4] * ab[0] + cs[5] * ab[1], cs[6] * ab[0] + cs[7] * ab[1]]
    dt = v1[0] * v2[1] - v1[1] * v2[0]
    if dt != 0 and K.ideal(dt) == a**2:
        x = matrix(K, [v1, v2])
        break
ok(x is not None)
mu = x.inverse().transpose()           # column form of a + a -> R + R
R1 = K.ideal(1)
for i in range(2):
    for j in range(2):
        ok(mu[i, j] * a + R1 == R1)    # alpha_ij M_j in N_i (M_j = a, N_i = R)
d = mu.det()
ok(K.ideal(d) * a * a == R1 * R1)      # N_1 N_2 = d M_1 M_2

print(f'ok s38_finite_quaternion_groups: {N} checks')
