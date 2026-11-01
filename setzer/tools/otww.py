# Mirror of Setzer's Section 4.5, the union of the distinguished sets: Def. 4.25 - Lemma 4.31,
# on a finite pool PL of OT.  WW is the union of the distinguished sets found on the pool
# (otag.distinguished); W, M, tau are those of the pool (otsec43, otsec4).  A test, not the
# infinite sets: a set whose witnesses need terms outside the pool is missed.
#   python3 otww.py lem N     4.26 (a), (b), 4.27, 4.28 (a), (b), 4.29 (a), (b), (c), the bound
#                             (y, z <=' m => y+z, phi_y z <' m+) and m in WW => m+ in WW,
#                             4.30 (with B = WW n (a+1)), 4.31 (a), (b)
#   python3 otww.py proof N   the steps of the proofs of 4.30, 4.31 (header of WW.seg)
# Reading of 4.29(b): Setzer's "z <=' C, z in C" is "x <=' C, x in C" (x below an element of
# C, so x in C by 4.23(a)); x =NF y+z, phi_y z is tested in the form x = y + z, phi_y z (the
# operations of Def. 2.10, as in Def. 4.14), and psi_y z in OT.
import sys
from otmirror import *
import otfun as Fn
from otsec4 import pool, tau, M, Fails
from otsec43 import W
from otclos import D, U
from otag import ag, seg, distinguished

def lem(N):
    PL = pool(N); PLs = set(PL); f = Fails(); cnt = {}
    def t(k): cnt[k] = cnt.get(k, 0) + 1
    ds = list(distinguished(PL))
    WW = set().union(*ds)
    Wf = lambda x: x in WW
    print(len(PL), 'terms,', len(ds), 'distinguished sets,', len(WW), 'points of WW')
    # 4.26(a) on the distinguished sets and on sets that are not
    cands = set(ds)
    for y in PL:
        Sg = frozenset(x for x in WW if lt(x, y)); cands.add(Sg)
        for z in Sg: cands.add(Sg - {z})
    for A in ds:
        for B in ds: cands.add(A | B)
    for X in cands:
        t('4.26a')
        if ag(X, PL) != seg(X, WW, PL): f('4.26a', sorted(map(show, X))[:6])
    if not ag(WW, PL): f('4.27')                                       # 4.26(b), 4.27
    for A in ds:                                                        # 4.28(b)
        for y in PL:
            t('4.28b')
            if not ag({x for x in A if lt(x, y)}, PL): f('4.28b', show(y))
    if not D(WW): f('4.29a D')                                          # 4.29(a)
    if not U(WW, lambda z: any(le(z, c) for c in WW), PL): f('4.29a U')
    for y in WW:                                                        # 4.29(b)
        for z in WW:
            for x, k in [(Fn.add(y, z), 'sum'), (Fn.phiF(y, z), 'phi'), (S(y, z), 'psi')]:
                if x in PLs and (k != 'psi' or (isR(y) and Fn.inC(y, z, z))):
                    t('4.29b ' + k)
                    if x not in WW: f('4.29b ' + k, show(y), show(z))
    for m in PL:                                                        # the bound
        for y in PL:
            for z in PL:
                if le(y, m) and le(z, m):
                    t('bound')
                    if Fn.add(y, z) in PLs and not lt(Fn.add(y, z), Fn.plus(m)): f('bound +', show(y), show(z), show(m))
                    if Fn.phiF(y, z) in PLs and not lt(Fn.phiF(y, z), Fn.plus(m)): f('bound phi', show(y), show(z), show(m))
    for m in WW:                                                        # m+ in WW, 4.29(c)
        if Fn.plus(m) in PLs:
            t('up')
            if Fn.plus(m) not in WW: f('up', show(m))
    for x in PL:
        if Fn.omF(x) in WW and Fn.omF(Fn.suc(x)) in PLs:
            t('4.29c')
            if Fn.omF(Fn.suc(x)) not in WW: f('4.29c', show(x))
    for a in PL:                                                        # 4.30
        if lt(a, I) and M(Wf, a):
            B = [x for x in WW if le(x, a)]
            if all(any(le(y, x) for x in B) for y in PL if tau(a, Wf, y)):
                t('4.30')
                if a not in WW: f('4.30', show(a))
    for x in WW:                                                        # 4.31(a)
        if lt(x, I) and Fn.omF(x) in PLs:
            t('4.31a')
            if Fn.omF(x) not in WW: f('4.31a', show(x))
    if S(I, Z) not in WW: f('4.31b 0')                                  # 4.31(b)
    for x in PL:
        if S(I, x) in WW and S(I, Fn.suc(x)) in PLs:
            t('4.31b')
            if S(I, Fn.suc(x)) not in WW: f('4.31b', show(x))
    print(cnt); f.report('Section 4.5')

def proof(N):
    # the steps of the proofs of 4.30 and 4.31 (header of WW.seg), with any distinguished
    # set D in place of WW where the step only uses Ag(D)
    from otsec4 import C
    PL = pool(N); PLs = set(PL); f = Fails(); cnt = {}
    def t(k): cnt[k] = cnt.get(k, 0) + 1
    ds = list(distinguished(PL))
    for D in ds:
        Df = lambda x, D=D: x in D
        WD_ = W(Df, PL)
        for d in PL:                                   # 4.30 (4): d in M(D) => d~ in C^d(D)
            if M(Df, d):
                t('4.30(4) til')
                if not C(d, Df, Fn.tilde(d)): f('4.30(4) til', show(d))
        for b in PL:                                   # 4.31(a): Omega_s in C^b(D) => s in C^b(D)
            for s in PL:
                if Fn.omF(s) in PLs and C(b, Df, Fn.omF(s)):
                    t('4.31a om-in')
                    if not C(b, Df, s): f('4.31a om-in', show(b), show(s))
        for a in D:                                    # 4.31(a): a in D \ Fi, a <' I => Omega_a in M(D)
            if lt(a, I) and Fn.omF(a) in PLs and Fn.omF(a) != a:
                t('4.31a M')
                if not M(Df, Fn.omF(a)): f('4.31a M', show(a))
                for z in PL:                           # Setzer's "C^a(D) c C^{Omega_a}(D)" (reading check)
                    if C(a, Df, z) and not C(Fn.omF(a), Df, z): t('4.31a C^a not c C^Omega_a'); break
        for c in D:                                    # 4.31(b): psi_I x in D => x+1 in C^{psi_I(x+1)}(D)
            if c[0] == 'S' and isI(c[1]):
                x = c[2]; e = Fn.suc(x)
                t('4.31b e')
                if not C(c, Df, x): f('4.31b x', show(c))
                if not C(S(I, e), Df, e): f('4.31b e', show(c))
                if not Fn.inC(I, x, e): f('4.31b inC', show(c))
    for a in PL:                                       # 4.31(a): y <' Omega_a, y~ = Omega_s => s <' a
        if not lt(a, I) or Fn.omF(a) not in PLs: continue
        for y in PL:
            if lt(y, Fn.omF(a)):
                s = [u for u in PL if Fn.omF(u) == Fn.tilde(y)]
                for u in s:
                    t('4.31a s<a')
                    if not lt(u, a): f('4.31a s<a', show(a), show(y), show(u))
                    if Fn.plus(y) != Fn.omF(Fn.suc(u)): f('4.31a y+', show(y))
    for x in [None] + PL:                              # 4.31(b): side conditions
        if x is None: c, e = Z, Z
        else:
            if not (isT(S(I, x)) and isOT(S(I, x))): continue
            c, e = S(I, x), Fn.suc(x)
        d = S(I, e)
        t('4.31b side')
        if not lt(Fn.suc(c), d): f('4.31b c+1', show(c))
        for n in range(4):
            if not lt(Fn.omN(n, Fn.suc(c)), d): f('4.31b W', show(c), n)
        for y in PL:
            if lt(y, d):
                t('4.31b mFi')
                if not le(Fn.mFi(y), c): f('4.31b mFi', show(c), show(y))
    print(cnt); f.report('proofs of 4.30, 4.31')

if __name__ == '__main__':
    {'lem': lem, 'proof': proof}[sys.argv[1]](int(sys.argv[2]))
