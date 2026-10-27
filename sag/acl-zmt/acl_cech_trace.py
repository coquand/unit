"""AUXILIARY (not checked by Unit; needs sympy). Usage: python3 acl_cech_trace.py 6
Follow the constructive proof (doc/zmt-gcd-cech.tex, Section 7) on the example of ACL §4.4:
   p = x - a + b x y + 2 b x^2 ,  q = y - b + a x^2 + a x y + b y^2 .
Laurent polynomials in X,Y,Z over Q[a,b] as dicts exponent -> sympy expr.
"""
import sys, itertools
from sympy import symbols, expand, Matrix, Poly, S, groebner, factor, Rational, QQ
a, b, x, y, T = symbols('a b x y T')

def clean(f): return {m: c for m, c in f.items() if c != 0}
def add(f, g, s=1):
    h = dict(f)
    for m, c in g.items(): h[m] = expand(h.get(m, 0) + s*c)
    return clean(h)
def scal(c, f): return clean({m: expand(c*v) for m, v in f.items()})
def mul(f, g):
    h = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            m = (m1[0]+m2[0], m1[1]+m2[1], m1[2]+m2[2]); h[m] = h.get(m, 0) + c1*c2
    return clean({m: expand(c) for m, c in h.items()})
def mono(i, j, k, c=1): return {(i, j, k): S(c)}
def power(f, n):
    r = mono(0, 0, 0)
    for _ in range(n): r = mul(r, f)
    return r
neg = lambda f: scal(-1, f)

# the charts
muP = mono(1, 0, 1); muQ = mono(0, 1, 1)
restP = add(scal(-a, mono(0, 0, 2)), scal(b, add(mono(1, 1, 0), mono(2, 0, 0, 2))))
restQ = add(scal(a, add(mono(2, 0, 0), mono(1, 1, 0))), scal(b, add(mono(0, 2, 0), mono(0, 0, 2, -1))))
P = add(muP, restP); Q = add(muQ, restQ)
thP = mono(-1, 0, -1); thQ = mono(0, -1, -1)
E = neg(mul(thP, restP))      # 1 - theta P
Ep = neg(mul(thQ, restQ))     # 1 - theta' Q
Zi = mono(0, 0, -1)
g = add(mul(muQ, P), mul(muP, Q), -1)

# sigma, pi, tau, delta
def isneg(e): return e < 0
def pi(q): return {m: c for m, c in q.items() if all(e < 0 for e in m)}
def sigma(q):
    XY, XZ, YZ = {}, {}, {}
    for m, c in q.items():
        if m[0] >= 0: YZ[m] = c
        elif m[1] >= 0: XZ[m] = -c
        elif m[2] >= 0: XY[m] = c
    return (XY, XZ, YZ)
def d1(bc):  # b_YZ - b_XZ + b_XY
    return add(add(bc[2], bc[1], -1), bc[0])
def d0(c):   # (cY - cX, cZ - cX, cZ - cY)
    return (add(c[1], c[0], -1), add(c[2], c[0], -1), add(c[2], c[1], -1))
def tau(bc):
    XY, XZ, YZ = bc
    cX, cY, cZ = {}, {}, {}
    ms = set(XY) | set(XZ) | set(YZ)
    for m in ms:
        En = [i for i in range(3) if m[i] < 0]
        if En == []:
            if m in XY: cY[m] = XY[m]
            if m in XZ: cZ[m] = XZ[m]
        elif En == [0]:
            if m in XY: cX[m] = -XY[m]
        elif En == [1]:
            if m in XY: cY[m] = XY[m]
        elif En == [2]:
            if m in XZ: cZ[m] = XZ[m]
    return (clean(cX), clean(cY), clean(cZ))
def tadd(u, v, s=1): return tuple(add(p, q, s) for p, q in zip(u, v))
def tscal(c, u): return tuple(scal(c, p) for p in u)
def tmul(f, u): return tuple(mul(f, p) for p in u)

dg = 4
gens = [(-i, -j, -(dg + 1 - i - j)) for i in range(1, dg) for j in range(1, dg) if dg + 1 - i - j >= 1]
print("deg g =", dg, " gens (all-negative of degree -5):", gens)

def step(n):
    w = ({}, mul(power(E, n), Zi), mul(power(Ep, n), Zi))
    S_ = {}
    for i in range(n): S_ = add(S_, mul(power(Ep, i), power(E, n - 1 - i)))
    qn = mul(mul(mono(-1, -1, -2), S_), Zi)   # (muP muQ)^-1 = X^-1 Y^-1 Z^-2
    assert add(d1(w), mul(g, qn), -1) == {}, "delta1 w_n = g q_n"
    rho = [qn.get(t, S(0)) for t in gens]
    R = tadd(w, sigma(mul(g, qn)) if False else tmul(g, sigma(qn)), -1)
    for t, r in zip(gens, rho):
        R = tadd(R, tscal(r, sigma(mul(g, mono(*t)))), -1)
    assert d1(R) == {}, "R is a cocycle"
    c = tau(R)
    assert tadd(d0(c), R, -1) == ({}, {}, {}), "delta0 tau R = R"
    return w, qn, rho, c

import time
steps = {}
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
t0 = time.time()
for n in range(1, NMAX + 1):
    steps[n] = step(n)
    if n <= 5: print("n =", n, " rho_n =", [factor(r) for r in steps[n][2]])
print("steps computed up to", NMAX, "in", round(time.time() - t0, 1), "s", flush=True)

# the noetherian relation: smallest N with rho_N = sum_{i<N} r_i rho_i, r_i in I^(N-i)
# (rho_n is homogeneous of degree n-1 in a, b; solve in degree N-1 over Q)
def homog_monos(d): return [a**(d - j) * b**j for j in range(d + 1)]
def find_relation(N):
    unknowns, cols = [], []
    for i in range(1, N):
        for mon in homog_monos(N - i):
            unknowns.append((i, mon)); cols.append([expand(mon * r) for r in steps[i][2]])
    target = steps[N][2]
    # coefficients of monomials of degree N-1 in a, b, for each of the 6 entries
    basis = homog_monos(N - 1)
    def vec(entries):
        v = []
        for e in entries:
            p = Poly(e, a, b) if e != 0 else None
            for mon in basis:
                v.append(p.coeff_monomial(mon) if p is not None else 0)
        return v
    M = Matrix([vec(c) for c in cols]).T if cols else Matrix([])
    t = Matrix(vec(target))
    if not cols: return None
    try:
        sol, params = M.gauss_jordan_solve(t)
    except ValueError:
        return None
    sol = sol.subs({p: 0 for p in params})
    r = {}
    for (i, mon), s_ in zip(unknowns, sol):
        r[i] = expand(r.get(i, 0) + s_ * mon)
    return r

for N in range(2, NMAX + 1):
    r = find_relation(N)
    print("N =", N, ":", "no relation" if r is None else {i: factor(v) for i, v in r.items()})
    if r is not None: break
if r is None: sys.exit(0)

# the correction h = (1 - sum r_i) z* - v,  v = v_N - sum r_i v_i
v = steps[N][3]
for i, ri in r.items(): v = tadd(v, tscal(ri, steps[i][3]), -1)
one_minus = expand(1 - sum(r.values()))
# s = res(Z h_Z) = (1 - sum r_i) - res(Z v_Z)
def res(f):  # dehomogenise on the chart Z
    return expand(sum(c * x**m[0] * y**m[1] for m, c in f.items()))
Zv = mul(mono(0, 0, 1), v[2])
assert all(m[0] >= 0 and m[1] >= 0 for m in Zv), "v_Z in Lambda_Z"
s = expand(one_minus - res(Zv))
print("s =", s)
print("s - 1 in I:", expand(s.subs({a: 0, b: 0})) == 1)

# compare with u = (1 + a x + b y)(1 + 2 b x + b y)^2 of ACL, and the integral equation of s in B
p = x - a + b*x*y + 2*b*x**2
q = y - b + a*x**2 + a*x*y + b*y**2
K = QQ.frac_field(a, b)
G = groebner([p, q], x, y, order='grevlex', domain=K)
print("Groebner basis of (p,q) over Q(a,b):", G.exprs)
std = [x**i * y**j for i in range(4) for j in range(4)]
std = [m for m in std if all(not Poly(m, x, y).monoms()[0] == Poly(m, x, y).monoms()[0] or True for _ in [0])]
# standard monomials: not divisible by a leading monomial
lms = [Poly(gi, x, y).monoms(order='grevlex')[0] for gi in G.exprs]
def divisible(m, l): return m[0] >= l[0] and m[1] >= l[1]
stdm = [(i, j) for i in range(6) for j in range(6) if not any(divisible((i, j), l) for l in lms)]
print("standard monomials:", stdm, " (dimension of B over Q(a,b) =", len(stdm), ")")
def coords(f):
    rem = G.reduce(expand(f))[1]
    pr = Poly(rem, x, y)
    return [pr.coeff_monomial(x**i * y**j) for (i, j) in stdm]
def charpoly(e):
    Mm = Matrix([coords(e * x**i * y**j) for (i, j) in stdm]).T
    return factor(Mm.charpoly(T).as_expr())
print("char poly of s :", charpoly(s))
u = expand((1 + a*x + b*y) * (1 + 2*b*x + b*y)**2)
print("char poly of u (ACL):", charpoly(u))
print("s - u in (p,q):", G.reduce(expand(s - u))[1] == 0)

from sympy import gcd as sgcd, degree, Poly as SP
X_, Y_, Z_ = symbols('X Y Z')
def topoly(f): return expand(sum(c * X_**m[0] * Y_**m[1] * Z_**m[2] for m, c in f.items()))
print("gcd(P,Q) =", sgcd(topoly(P), topoly(Q)))
for name, e in [("s x", expand(s*x)), ("s y", expand(s*y))]:
    cp = charpoly(e)
    print("char poly of", name, "monic, coefficients in Q[a,b]:", SP(cp, T).LC() == 1 and all(c.is_polynomial(a, b) for c in SP(cp, T).all_coeffs()))
print("total degree of s in x,y:", SP(s, x, y).total_degree(), "; in a,b:", SP(s, a, b).total_degree(), "; terms:", len(SP(s, x, y, a, b).terms()))
print("s mod I^2:", expand(s.subs({a: 0, b: 0}) + sum(s.diff(v).subs({a: 0, b: 0}) * v for v in (a, b))))
tt = symbols('tt')
sh = expand(s.subs({a: tt*a, b: tt*b}))
print("s mod I^3:", expand(sum(SP(sh, tt).coeff_monomial(tt**k) for k in range(3))))
print("s mod I^4, degree-3 part:", factor(SP(sh, tt).coeff_monomial(tt**3)))
