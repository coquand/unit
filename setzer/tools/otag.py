# Mirror of Setzer's Section 4.4, distinguished sets: Def. 4.18 - Lemma 4.24, on a finite
# pool PL of OT (W(A) as in otsec43.py: the least fixed point restricted to PL).
#   python3 otag.py ag N      list the distinguished sets found (A = W(A) n a, by iteration)
#   python3 otag.py lem N     Remark 4.20, Lemma 4.21(b), 4.23 (a), (b), (c), 4.24, and the
#                             transfer lemma (A n z = B n z, x in W(A), x <=' z => x in W(B))
# Reading of 4.23(a): "upward closed bounded by A" with the bound the class
#   Dn(A) = {z | z <=' c for some c in A}; with the bound A itself (z in A) the statement
#   is trivial (z in A gives z in A); Dn(A) is the one tested.
import sys
from otmirror import *
import otfun as Fn
from otsec4 import pool, C, tau, M, Fails, OM1, goodClasses
from otsec43 import W
from otclos import D, U

def seg(A, B, PL):      # A [= B on the pool: A c OT, and A|x = B|x for x in A (A|x = A n (x+1))
    return all(x in B for x in A) and all((y in A) == (y in B) for x in A for y in PL if le(y, x))
def ag(A, PL): return seg(A, W(lambda x: x in A, PL), PL)

def distinguished(PL):
    out = {}
    for a in PL + [None]:
        A = set()
        for _ in range(60):
            WAs = W(lambda x, A=A: x in A, PL)
            B = {x for x in WAs if a is None or lt(x, a)}
            if B == A: break
            A = B
        else: continue
        if ag(A, PL): out[frozenset(A)] = a
    # segments A n y (Lemma 4.28(b)) of the sets found
    for A in list(out):
        for y in PL:
            B = frozenset(x for x in A if lt(x, y))
            if B not in out and ag(B, PL): out[B] = ('seg', y)
    return out

def agList(N):
    PL = pool(N); ds = distinguished(PL)
    for A, a in sorted(ds.items(), key=lambda p: len(p[0])):
        print(len(A), show(a) if isinstance(a, tuple) and a[0] != 'seg' else a, sorted(map(show, A))[:8])

def lem(N):
    PL = pool(N); PLs = set(PL); f = Fails(); cnt = {}
    def t(k): cnt[k] = cnt.get(k, 0) + 1
    ds = distinguished(PL)
    for A in ds:
        Af = lambda x, A=A: x in A
        WA = W(Af, PL)
        t('Ag')
        for a in A:                                               # Remark 4.20
            if {y for y in PL if tau(a, Af, y)} != {y for y in A if lt(y, a)}: f('4.20', a)
        for x in A:                                               # 4.21(b)
            if lt(x, OM1) and not all(z in A for z in PL if le(z, x)): f('4.21b', x)
        Dn = lambda z, A=A: any(le(z, c) for c in A)
        if not D(A): f('4.23a D', sorted(map(show, A)))
        if not U(A, Dn, PL): f('4.23a U bounded by Dn A', sorted(map(show, A))[:5])
        for k in A:                                               # 4.23(b)
            if not isR(k): continue
            for c in A:
                d = S(k, c)
                if Fn.inC(k, c, c) and d in PLs:
                    t('4.23b')
                    if d not in A: f('4.23b', k, c)
        Ap = {y for z in A for y in WA if lt(y, Fn.plus(z))} | {Fn.plus(z) for z in A}   # 4.23(c)
        if all(y in PLs for y in Ap):
            t('4.23c')
            if not ag(Ap, PL): f('4.23c Ag', sorted(map(show, A))[:5])
            if not A <= Ap: f('4.23c sub')
    Wd = {A: W(lambda y, A=A: y in A, PL) for A in ds}           # 4.24
    bounds = {A: [b for b in PL if A == {x for x in Wd[A] if lt(x, b)}] for A in ds}
    for A0 in ds:
        for A1 in ds:
            for b0 in bounds[A0]:
                for b1 in bounds[A1]:
                    if not le(b0, b1): continue
                    t('4.24')
                    if A0 != {x for x in A1 if lt(x, b0)}: f('4.24', b0, b1)
    cs = goodClasses(PL)                                          # transfer
    Ws = {n: W(A, PL) for (n, A) in cs}
    for (n, A) in cs:
        for (m, B) in cs:
            for z in PL:
                if all(A(x) == B(x) for x in PL if lt(x, z)):
                    t('transfer')
                    for x in Ws[n]:
                        if le(x, z) and x not in Ws[m]: f('transfer', n, m, z, x)
    print(len(PL), 'terms', cnt); f.report('Section 4.4')

if __name__ == '__main__':
    {'ag': agList, 'lem': lem}[sys.argv[1]](int(sys.argv[2]))
