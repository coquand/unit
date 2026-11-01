# Mirror of unit/setzer/OT.seg: the same clauses and the same recursion, in Python, for exhaustive tests (tools/checks.py).
import sys, itertools, functools
sys.setrecursionlimit(100000)

Z = ('Z',); I = ('I',)
def P(a, t): return ('P', a, t)
def F(a, b): return ('F', a, b)
def S(p, b): return ('S', p, b)
def O(a): return ('O', a)

def isZero(x): return x[0] == 'Z'
def isI(x): return x[0] == 'I'
def isSuc(x):
    if x[0] == 'P': return isSuc(x[2])
    if x[0] == 'F': return isZero(x[1]) and isZero(x[2])
    return False
def isR(x): return (x[0] == 'O' and isSuc(x[1])) or x[0] == 'I'
def isFi(x): return (x[0] == 'S' and isI(x[1])) or x[0] == 'I'
def isG(x): return x[0] in ('S', 'O', 'I')
def isA(x): return x[0] in ('F', 'S', 'O', 'I')
@functools.lru_cache(None)
def isT(x):
    k = x[0]
    if k == 'Z' or k == 'I': return True
    if k == 'P': return isA(x[1]) and isT(x[1]) and not isZero(x[2]) and isT(x[2])
    if k == 'F': return isT(x[1]) and isT(x[2])
    if k == 'S': return isR(x[1]) and isT(x[1]) and isT(x[2])
    if k == 'O': return not isZero(x[1]) and isT(x[1])

def eqT(x, y): return x == y

def other(l): return (l, not l)
def otherR(r): return (not r, r)
def leOf(c, e): return c[0] or e

@functools.lru_cache(None)
def cmp2(x, y):
    kx, ky = x[0], y[0]
    if kx == 'Z':
        return (False, False) if ky == 'Z' else other(True)
    if ky == 'Z':
        return otherR(True)
    if kx == 'P':
        x0, xs = x[1], x[2]
        if ky == 'P':
            if x == y: return (False, False)
            h = cmp2(x0, y[1]); e = x0 == y[1]; t = cmp2(xs, y[2])
            return (h[0] or (e and t[0]), h[1] or (e and t[1]))
        h = cmp2(x0, y); e = y == x0
        return (h[0], h[1] or e)
    if ky == 'P':
        h = cmp2(x, y[1]); e = x == y[1]
        return (h[0] or e, h[1])
    if kx == 'F':
        xa, xb = x[1], x[2]
        if ky == 'F':
            if x == y: return (False, False)
            yc, yd = y[1], y[2]
            ac = cmp2(xa, yc); bY = cmp2(xb, y); eac = xa == yc
            bd = cmp2(xb, yd); xd = cmp2(x, yd); exd = x == yd; eyb = y == xb
            return ((ac[0] and bY[0]) or (eac and bd[0]) or (ac[1] and leOf(xd, exd)),
                    (ac[1] and xd[1]) or (eac and bd[1]) or (ac[0] and (bY[1] or eyb)))
        return other(cmp2(xa, y)[0] and cmp2(xb, y)[0])
    if ky == 'F':
        return otherR(cmp2(x, y[1])[1] and cmp2(x, y[2])[1])
    if kx == 'S':
        xp, xb = x[1], x[2]; ip = isI(xp)
        if ky == 'S':
            if x == y: return (False, False)
            yq, yd = y[1], y[2]; iq = isI(yq)
            epq = xp == yq; bd = cmp2(xb, yd); pq = cmp2(xp, yq); xq = cmp2(x, yq); pY = cmp2(xp, y)
            return ((epq and bd[0]) or (not ip and not iq and pq[0]) or (ip and not iq and xq[0]) or (not ip and iq and pY[0]),
                    (epq and bd[1]) or (not iq and not ip and pq[1]) or (iq and not ip and pY[1]) or (not iq and ip and xq[1]))
        if ky == 'O':
            l = leOf(cmp2(x, y[1]), x == y[1]) if ip else leOf(cmp2(xp, y), xp == y)
            return other(l)
        # ky == 'I'
        return other(True if ip else leOf(cmp2(xp, y), xp == y))
    if ky == 'S':
        yq = y[1]; iq = isI(yq)
        if kx == 'O':
            r = (cmp2(x[1], y)[1] or y == x[1]) if iq else (cmp2(x, yq)[1] or yq == x)
            return otherR(r)
        return otherR(True if iq else (cmp2(x, yq)[1] or yq == x))
    if kx == 'O':
        if ky == 'O':
            return (False, False) if x == y else cmp2(x[1], y[1])
        return other(cmp2(x[1], I)[0])
    # kx == 'I'
    if ky == 'O':
        return otherR(cmp2(x, y[1])[1])
    return (False, False)

def lt(x, y): return cmp2(x, y)[0]
def le(x, y): return lt(x, y) or x == y

def G(p, x):
    k = x[0]
    if k in ('Z', 'I'): return []
    if k == 'P' or k == 'F': return G(p, x[1]) + G(p, x[2])
    if k == 'O': return G(p, x[1])
    kk, b = x[1], x[2]
    gk, gb = G(p, kk), G(p, b)
    if isI(kk):
        return [b] + gk + gb if (isI(p) or le(p, x)) else []
    if le(p, kk): return [b] + gk + gb
    return gk if isI(p) else []

def allLt(M, y): return all(lt(h, y) for h in M)
def crit(x, y):
    if y[0] == 'F': return lt(x, y[1])
    if isG(y): return lt(x, y)
    return False
def hd(x): return x[1] if x[0] == 'P' else x
@functools.lru_cache(None)
def isOT(x):
    k = x[0]
    if k in ('Z', 'I'): return True
    if k == 'P': return isA(x[1]) and isOT(x[1]) and not isZero(x[2]) and isOT(x[2]) and le(hd(x[2]), x[1])
    if k == 'F': return isOT(x[1]) and isOT(x[2]) and not crit(x[1], x[2]) and not (isZero(x[2]) and isG(x[1]))
    if k == 'S': return isR(x[1]) and isOT(x[1]) and isOT(x[2]) and allLt(G(x[1], x[2]), x[2])
    if k == 'O': return isOT(x[1]) and not isFi(x[1]) and not isZero(x[1])

# enumeration of raw terms by size (number of constructors)
@functools.lru_cache(None)
def terms(n):
    if n <= 0: return ()
    out = []
    if n == 1: out += [Z, I]
    out += [O(a) for a in terms(n - 1)]
    for k in range(1, n - 1):
        for a in terms(k):
            for b in terms(n - 1 - k):
                out += [P(a, b), F(a, b), S(a, b)]
    return tuple(out)

def show(x):
    k = x[0]
    if k == 'Z': return '0'
    if k == 'I': return 'I'
    if k == 'O': return 'Om(' + show(x[1]) + ')'
    if k == 'P': return '(' + show(x[1]) + ' + ' + show(x[2]) + ')'
    if k == 'F': return 'phi(' + show(x[1]) + ',' + show(x[2]) + ')'
    return 'psi[' + show(x[1]) + '](' + show(x[2]) + ')'

