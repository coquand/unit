# Mirror of Setzer's Definitions 2.10, 2.11, 2.13 (functions on OT), for the tests of
# Remarks 2.12, 2.14, 2.15 in checks.py.  Terms as in otmirror.py.
from otmirror import *

ONE = F(Z, Z)

# a sum as the list of its summands: 0 = [], an atom = [a]
def summands(x):
    if isZero(x): return []
    if x[0] == 'P': return [x[1]] + summands(x[2])
    return [x]
def build(xs):
    if not xs: return Z
    if len(xs) == 1: return xs[0]
    return P(xs[0], build(xs[1:]))

def isOTs(x): return isT(x) and isOT(x)
def lto(x, y): return isOTs(x) and isOTs(y) and lt(x, y)       # x < y on OT
def leo(x, y): return isOTs(x) and isOTs(y) and le(x, y)

# 2.10(a) a + b
def add(a, b):
    xs, ys = summands(a), summands(b)
    if not ys: return a
    j = max([i for i in range(len(xs)) if le(ys[0], xs[i])], default=-1)
    return build(xs[:j + 1] + ys)
# 2.10(b) a . n
def mul(a, n):
    r = Z
    for _ in range(n): r = add(r, a)
    return r
# 2.10(c) phi_a b
def crit(a, b):  # b in Cr(a)
    if b[0] == 'F': return lt(a, b[1])
    if isG(b): return lt(a, b)
    return False
def phiF(a, b):
    if crit(a, b): return b
    if isZero(b) and isG(a): return a
    return F(a, b)
# 2.10(d) Omega_a, (e) Omega^n_a
def omF(a):
    if isZero(a): return Z
    if isFi(a): return a
    return O(a)
def omN(n, a):
    for _ in range(n): a = omF(a)
    return a
def suc(a): return add(a, ONE)

# 2.13(a) kappa^-
def pred1(a):  # s with a = s+1, a in Suc
    xs = summands(a); return build(xs[:-1])
def kminus(k):
    if isI(k): return Z
    return omF(pred1(k[1]))

# 2.13(b): returns (tilde, plus, minusFi, plusFi)
def card(a):
    k = a[0]
    if k == 'Z': return (Z, O(ONE), Z, S(I, Z))
    if k == 'P': return card(a[1])
    if k == 'F': return card(a[1] if le(a[2], a[1]) else a[2])
    if k == 'S' and not isI(a[1]):
        b = a[1]; cb = card(b)
        return (kminus(b), b, cb[2], cb[3])
    if k == 'S': return (a, omF(suc(a)), a, S(I, suc(a[2])))
    if k == 'O':
        cb = card(a[1]); return (a, omF(suc(a[1])), cb[2], cb[3])
    return (I, O(suc(I)), I, I)
def tilde(a): return card(a)[0]
def plus(a): return card(a)[1]
def mFi(a): return card(a)[2]
def pFi(a): return card(a)[3]
# 2.13(c)
def mI(a): return Z if lt(a, I) else I

def length(x):
    if x[0] in ('Z', 'I'): return 1
    if x[0] == 'O': return 1 + length(x[1])
    return 1 + length(x[1]) + length(x[2])

# C_k(a), and b in C_k(a)
def inC(k, a, b): return isOTs(b) and allLt(G(k, b), a)
