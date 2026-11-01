# Mirror of Setzer's Section 4.6, Gamma_c: Def. 4.32 - Lemma 4.38, on a finite pool PL of OT,
# in the form proved in GammaI.seg (header there).  WW is the union of the distinguished sets
# of the pool (otag.distinguished), as in otww.py.
#   python3 otgam.py lem N    4.37 (C_I^D(c) = Gamma^omega for every D distinguished or D = WW
#                             with tau^D(psi_I c) c D; every stage c C_I^D(c)), the steps of the
#                             completeness proof, the order facts used, and 4.38 (a), (b), (c)
#   python3 otgam.py xlem N   the same on pool(N) plus psi_k y with k = Omega_{I+1}, Omega_{I+2}
# Gamma_c(A) (GammaI.seg):  d in OT n C_I(c), and
#   (Str) 0, I;  d = (x0, xs) with x0, xs in A;  phi_x0 x1 with x0, x1 in A;  Omega_x0 with x0 in A;
#         psi_k y with psi_I c <' k and k, y in A;
#   (Pc)  d in D n k for some k in A with k <' psi_I c.
import sys
from otmirror import *
import otfun as Fn
from otsec4 import pool, tau, M, C, Fails
from otsec43 import W
from otag import distinguished

def gam(c, Df, A, PL):
    a = S(I, c)
    def strc(d):
        k = d[0]
        if k in ('Z', 'I'): return True
        if k in ('P', 'F'): return d[1] in A and d[2] in A
        if k == 'O': return d[1] in A
        return lt(a, d[1]) and d[1] in A and d[2] in A
    def pc(d): return any(lt(k, a) and Df(d) and lt(d, k) for k in A)
    return {d for d in PL if Fn.inC(I, c, d) and (strc(d) or pc(d))}

def stages(c, Df, PL):
    G = [set()]
    while True:
        nxt = G[-1] | gam(c, Df, G[-1], PL)
        if nxt == G[-1]: return G
        G.append(nxt)

def subterms(x):
    out = {x}
    for y in x[1:]: out |= subterms(y)
    return out

# pool(N) and the subterms of psi_k y with k = Omega_{I+1}, Omega_{I+2} (not in pool(7))
def xpool(N):
    O1 = O(P(I, Fn.ONE)); O2 = O(P(I, P(Fn.ONE, Fn.ONE)))
    ex = [S(O1, Z), S(O1, Fn.ONE), S(O1, I), S(O2, Z), S(O2, S(O1, Z)), S(I, S(O1, Z)), S(I, S(O1, Fn.ONE)),
          F(Z, S(O1, Z)), P(S(O1, I), S(O1, Z))]
    PL = pool(N); PLs = set(PL)
    for e in ex:
        for x in subterms(e):
            if x not in PLs and isT(x) and isOT(x): PL.append(x); PLs.add(x)
    return PL

def lem(N, PL=None):
    if PL is None: PL = pool(N)
    PLs = set(PL); f = Fails(); cnt = {}
    def t(k): cnt[k] = cnt.get(k, 0) + 1
    ds = list(distinguished(PL))
    WW = set().union(*ds)
    print(len(PL), 'terms,', len(ds), 'distinguished sets,', len(WW), 'points of WW')
    cs = [c for c in PL if S(I, c) in PLs]
    # order facts
    for x in PL:
        if x[0] == 'S' and not isI(x[1]):
            k = x[1]; t('psi_k y')
            if Fn.plus(x) != k: f('up psi', show(x))
            if not lt(x, k): f('psi < k', show(x))
            if le(I, k) and lt(x, I): f('I <= k, psi_k y < I', show(x))
    for c in cs:
        for u in PL:
            if lt(u, I):
                t('cs-I')
                if Fn.inC(I, c, u) != lt(u, S(I, c)): f('cs-I', show(c), show(u))
    for D, nm in [(d, 'D') for d in ds] + [(WW, 'WW')]:
        Df = lambda x, D=D: x in D
        for c in cs:
            a = S(I, c)
            if not all(y in D for y in PL if tau(a, Df, y)): continue
            t('hyp ' + nm)
            CW = {x for x in PL if Fn.inC(I, c, x) and C(a, Df, x)}
            G = stages(c, Df, PL)
            for g in G:
                if not g <= CW: f('sound ' + nm, show(c), sorted(map(show, g - CW))[:3])
            if not CW <= G[-1]: f('complete ' + nm, show(c), sorted(map(show, CW - G[-1]))[:3])
            # the steps of the completeness proof
            for x in CW:
                if x[0] in ('P', 'F'):
                    t('parts ' + nm)
                    if not (C(a, Df, x[1]) and C(a, Df, x[2])): f('parts', show(x))
                if x[0] == 'O' and not C(a, Df, x[1]): f('parts O', show(x))
                if x[0] == 'S':
                    k, y = x[1], x[2]
                    own = Df(x) and lt(x, a)
                    if not own:
                        t('psi struct ' + nm)
                        if not le(I, k): f('psi struct k<I', show(x))
                    elif isI(k):
                        t('psi_I leaf ' + nm)
                        if not C(a, Df, y): f('psi_I leaf y', show(x))
                    else:
                        t('psi_k leaf ' + nm)
                        if le(I, k): f('psi_k leaf I<=k', show(x))
                        if nm == 'WW' and k not in D: f('psi_k leaf k in WW', show(x))
                        if not lt(k, a): f('psi_k leaf k<a', show(x))
    # 4.38
    Wf = lambda x: x in WW
    WWW = W(Wf, PL)
    for c in PL:
        a = S(I, c)
        if a in PLs and M(Wf, a) and all(y in WW for y in PL if tau(a, Wf, y)):
            t('4.38a')
            if a not in WW: f('4.38a', show(c))
    for x in PL:
        if lt(x, I) and M(Wf, x) and all(y in WW for y in PL if tau(x, Wf, y)):
            t('4.38b')
            if x not in WW: f('4.38b', show(x))
            mf = Fn.mFi(x)
            if lt(S(I, Z), x) and lt(mf, x) and not tau(x, Wf, mf): f('4.38b mFi', show(x))
            if not lt(x, Fn.pFi(x)): f('4.38b pFi', show(x))
    for x in PL:
        if lt(x, I):
            t('4.38c')
            if (x in WW) != (x in WWW): f('4.38c', show(x))
    print(cnt); f.report('Section 4.6')

if __name__ == '__main__':
    if sys.argv[1] == 'xlem': lem(0, xpool(int(sys.argv[2])))
    else: {'lem': lem}[sys.argv[1]](int(sys.argv[2]))
