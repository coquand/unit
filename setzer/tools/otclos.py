# Mirror of Setzer's Section 4.3, closure properties: Def. 4.14, Remark 4.15, Lemmas 4.16, 4.17,
# and the comparison x, y <' cat x y that Def. 4.14(a) needs.
#   python3 otclos.py catlt N   x, y in T', x, y /= 0:  x <' cat x y;  y <' cat x y when cat x y in OT
#                               (and: y <' cat x y can fail on T' outside OT)
import sys
from otmirror import *
import otfun as Fn
from otsec4 import Fails

def cat(x, y):
    if isZero(x): return y
    if x[0] == 'P': return P(x[1], cat(x[2], y))
    return P(x, y)

def tpool(N): return [x for n in range(1, N + 1) for x in terms(n) if isT(x)]

def catlt(N):
    T = [x for x in tpool(N) if not isZero(x)]; f = Fails(); n = m = 0
    for x in T:
        for y in T:
            z = cat(x, y); n += 1
            if not lt(x, z): f('x', x, y)
            if isOT(z):
                m += 1
                if not lt(y, z): f('y', x, y)
            elif not lt(y, z): f('y-outside-OT (expected)', x, y)
    print(n, 'pairs in T\',', m, 'with cat x y in OT'); f.report('x, y <\' cat x y')

# ---- Def. 4.14 on a finite pool PL (the quantifiers "z in OT" range over PL) ----
# NF decompositions of z in OT: splits(z) = all (x, y) with z =NF x + y; lastsplit = the =NF' one.
def splits(z):
    xs = Fn.summands(z)
    return [(Fn.build(xs[:i]), Fn.build(xs[i:])) for i in range(1, len(xs))] if z[0] == 'P' else []
def lastsplit(z): return splits(z)[-1:]

def wdParts(z):          # what 4.14(a) asks to be in A when z is
    if z[0] == 'P': return list(lastsplit(z)[0])
    if z[0] == 'F': return [z[1], z[2]]
    if z[0] == 'O': return [z[1]]
    if z[0] == 'S': return [Fn.kminus(z[1])]
    return []
def WD(A):
    return all(p in A for z in A for p in wdParts(z))
def D(A):                # 4.14(b), x^{-1} read as x^{-I}
    return (WD(A) and all(p in A for z in A for s in splits(z) for p in s)
            and all(Fn.tilde(x) in A and Fn.mFi(x) in A and Fn.mI(x) in A for x in A)
            and all(Fn.kminus(k) in A for k in A if isR(k)))
def WU(A, Cb, PL):       # 4.14(c), bounded by the class Cb
    for z in PL:
        if not Cb(z) or z in A: continue
        if z[0] == 'P' and all(p in A for p in lastsplit(z)[0]): return False
        if z[0] == 'F' and z[1] in A and z[2] in A: return False
        if z[0] == 'O' and z[1] in A: return False
        if z in (Z, I): return False
    return True
def U(A, Cb, PL):        # 4.14(d)
    PLs = set(PL)
    for z in (Z, I):
        if z in PLs and Cb(z) and z not in A: return False
    for x in A:
        for z in [Fn.omF(x), Fn.plus(x)] + [f(x, y) for y in A for f in (Fn.add, Fn.phiF)]:
            if z in PLs and Cb(z) and z not in A: return False
    return True

def close(seed, Cb, PL):  # the least superset of seed, inside PL, weakly downward and weakly upward closed bounded by Cb
    A = set(seed); PLs = set(PL)
    while True:
        new = {p for z in A for p in wdParts(z) if p in PLs} - A
        new |= {z for z in PL if Cb(z) and z not in A and (
                  z in (Z, I) or (z[0] == 'P' and all(p in A for p in lastsplit(z)[0]))
                  or (z[0] == 'F' and z[1] in A and z[2] in A) or (z[0] == 'O' and z[1] in A))}
        if not new: return A
        A |= new

def rem415(N):
    import random
    from otsec4 import pool
    PL = pool(N); f = Fails(); random.seed(5); n = 0
    bounds = [c for c in PL if not isZero(c)][::max(1, len(PL) // 40)] + [None]
    for c in bounds:
        for le_reading in (False, True):
            Cb = (lambda z: True) if c is None else (lambda z, c=c: le(z, c)) if le_reading else (lambda z, c=c: lt(z, c))
            below = [z for z in PL if Cb(z)]
            for _ in range(15):
                A = close(random.sample(below, min(2, len(below))), Cb, PL)
                if not all(Cb(x) for x in A) or not (WD(A) and WU(A, Cb, PL)): continue
                n += 1
                tag = 'OT' if c is None else ('<=c' if le_reading else '<c')
                if not D(A): f('D ' + tag, c, sorted(map(show, A))[:6])
                if not U(A, Cb, PL): f('U ' + tag, c)
    print(n, 'closed classes'); f.report('Remark 4.15')

def lem416(N):
    from otsec4 import pool, C, tau, M, goodClasses, classes
    from otsec43 import W
    PL = pool(N); f = Fails(); cnt = {}
    def t(k): cnt[k] = cnt.get(k, 0) + 1
    OTb = lambda z: True
    for (n, A) in goodClasses(PL):
        WA = W(A, PL); MA = {x for x in PL if M(A, x)}
        for a in PL:
            at = Fn.tilde(a)
            if not WD({x for x in PL if A(x) and lt(x, at)}): continue
            t('a')
            Ca = {x for x in PL if C(a, A, x)}
            if not D(Ca): f('C D', n, a)
            if not U(Ca, OTb, PL): f('C U', n, a)
            Ta = {x for x in Ca if lt(x, a)}
            if not D(Ta): f('tau D', n, a)
            if not U(Ta, lambda z: lt(z, a), PL): f('tau U<a', n, a)
            if not U(Ta, lambda z: le(z, a), PL): t('tau U<=a fails (reading check)')
            ap = Fn.plus(a)
            if not D({x for x in WA if lt(x, ap)}): f('W D', n, a)
            if not D({x for x in MA if lt(x, ap)}): f('M D', n, a)
        for k in PL:                                                  # (b)
            if not isR(k): continue
            Ak = {x for x in PL if A(x) and lt(x, k)}
            seg = all(x in WA for x in Ak) and all((y in Ak) == (y in WA) for x in Ak for y in PL if le(y, x))
            if seg:
                t('b')
                if not WD(Ak): f('b', n, k)
    print(cnt); f.report('Lemma 4.16')

def lem417(N):
    from otsec4 import pool, M, goodClasses
    from otsec43 import W
    PL = pool(N); f = Fails(); cnt = {}
    def t(k): cnt[k] = cnt.get(k, 0) + 1
    for (n, A) in goodClasses(PL):
        WA = W(A, PL)
        if Z not in WA: f('a', n)
        for k in PL:                                                  # (b), any k in OT (Setzer: k in R)
            if all((A(x) and lt(x, k)) == (x in WA and lt(x, k)) for x in PL):
                t('b' if isR(k) else 'b, k not in R')
                kp = Fn.plus(k); B = {x for x in WA if lt(x, kp)}
                if not D(B): f('b D', n, k)
                if not U(B, lambda z: lt(z, kp), PL): f('b U', n, k)
        for kk in WA:                                                 # (c)
            if not isR(kk): continue
            for y in WA:
                if not Fn.inC(kk, y, y): continue
                d = S(kk, y)
                if d not in set(PL): continue
                zm = kk if le(y, kk) else y
                for z in WA:                                          # (c), any z in W(A) above k, y
                    if not (le(kk, z) and le(y, z)): continue
                    zt = Fn.tilde(z)
                    if not all((x in WA and lt(x, zt)) == (A(x) and lt(x, zt)) for x in PL): continue
                    t('c' if z == zm else 'c, z > max')
                    if d not in WA: f('c', n, kk, y, z)
    print(cnt); f.report('Lemma 4.17')

if __name__ == '__main__':
    {'catlt': catlt, 'rem415': rem415, 'lem416': lem416, 'lem417': lem417}[sys.argv[1]](int(sys.argv[2]))
