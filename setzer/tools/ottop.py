# Mirror of Setzer's Section 4.7: Definition 4.39 - Theorem 4.41, on a finite pool PL of OT,
# in the form proved in Top.seg (header there).  WW is the union of the distinguished sets of
# the pool (otag.distinguished), W(A) the least fixed point restricted to the pool (otsec43).
#   python3 ottop.py lem N   pool(N) plus the terms around Omega_{I+1}, Omega_{I+2}, Omega_{I+3}:
#     the base:   tau^WW(I) c WW, by its proof (y <' psi_I 0, or y^{-Fi} = psi_I b in C^I(WW),
#                 y in C^{psi_I(b+1)}(WW)), and E(0), F(0)
#     the step:   A = WW_j, B = WW_{j+1}, k = Omega_{I+j}, k' = Omega_{I+j+1} = k+:
#                 A c B, B c M(B), A n k = B n k, W(A) n k' = W(B) n k' (4.13(b)), E(j+1),
#                 A+ n k' = B n k', k' in W(A+) (ap-wup), F(j+1)
#     4.40:       Ag(WW_i), Omega_{I+i} in WW_{i+1}, WW_i = WW_{i+1} n Omega_{I+i}
#     4.41:       Omega_1 in WW_0, Omega_{I+n} in C_{Omega_1}(Omega_{I+n}),
#                 psi_{Omega_1} Omega_{I+n} in WW_{n+1}, and every y <' psi_{Omega_1} Omega_{I+n}
#                 of the pool is in WW_{n+1} n Omega_1
# E(i): WW_i = W(WW_i) n Omega_{I+i};  F(i): Omega_{I+i} in W(WW_i).
import sys
from otmirror import *
import otfun as Fn
from otsec4 import pool, tau, M, C, Fails, OM1
from otsec43 import W
from otag import ag, distinguished

ONE = Fn.ONE
def ones(m):                      # (1, .., 1), m+1 summands
    x = ONE
    for _ in range(m): x = P(ONE, x)
    return x
def iN(n): return I if n == 0 else P(I, ones(n - 1))      # I + n
def kN(n): return Fn.omF(iN(n))                          # Omega_{I+n}

def subterms(x):
    out = {x}
    for y in x[1:]: out |= subterms(y)
    return out

def xpool(N):
    K = [kN(i) for i in range(4)]
    ex = [P(I, ONE), P(I, I), F(Z, I), F(ONE, I), F(I, Z), O(P(I, ONE)), P(K[1], ONE), P(K[1], K[1]),
          F(Z, K[1]), O(K[1]) if isOT(O(K[1])) else Z,
          S(K[1], Z), S(K[1], ONE), S(K[1], I), S(K[2], Z), S(K[2], K[1]), S(K[3], Z), S(K[2], S(K[1], Z)),
          S(I, S(K[1], Z)), S(I, K[1]), S(I, P(I, ONE)), S(I, I), F(Z, S(K[1], Z))]
    ex += [S(OM1, k) for k in K] + [S(OM1, ONE), S(OM1, I)]
    PL = pool(N); PLs = set(PL)
    for e in ex + K:
        for x in subterms(e):
            if x not in PLs and isT(x) and isOT(x): PL.append(x); PLs.add(x)
    return PL

def lem(N):
    PL = xpool(N); PLs = set(PL); f = Fails(); cnt = {}
    def t(k): cnt[k] = cnt.get(k, 0) + 1
    ds = list(distinguished(PL))
    WW = set().union(*ds); Wf = lambda x: x in WW
    print(len(PL), 'terms,', len(ds), 'distinguished sets,', len(WW), 'points of WW')
    K = [kN(i) for i in range(5)]
    for i in range(4):
        if not (isT(iN(i)) and isOT(iN(i)) and isOT(K[i])): f('OK k', i)
        if Fn.suc(iN(i)) != iN(i + 1): f('iN-suc', i)
        if Fn.plus(K[i]) != K[i + 1]: f('kN-up', i)
        if not lt(K[i], K[i + 1]): f('lt-k', i)
        t('kN')
    # the base: tau^WW(I) c WW
    for y in PL:
        if tau(I, Wf, y):
            t('tau-I')
            if y not in WW: f('tau-I', show(y))
            if lt(y, S(I, Z)):
                if not C(S(I, Z), Wf, y): f('tau-I C^{psi_I 0}', show(y))
                continue
            mf, pf = Fn.mFi(y), Fn.pFi(y)
            if not (mf[0] == 'S' and isI(mf[1]) and pf == S(I, Fn.suc(mf[2]))): f('tau-I form', show(y))
            if not C(I, Wf, mf): f('tau-I mFi in C^I', show(y))
            if mf in PLs and mf not in WW: f('tau-I mFi in WW', show(y))
            if not lt(y, pf): f('tau-I y < pFi', show(y))
            if pf in PLs:
                t('tau-I pFi')
                if pf not in WW: f('tau-I pFi in WW', show(y))
                if not C(pf, Wf, y): f('tau-I C^{pFi}', show(y))
    # the classes WW_i
    WWs = [{x for x in WW if lt(x, I)}]
    for i in range(3):
        A = WWs[i]
        WWs.append({x for x in W(lambda z, A=A: z in A, PL) if lt(x, K[i + 1])})
    print('sizes of WW_i:', [len(A) for A in WWs])
    for i in range(3):
        A = WWs[i]; Af = lambda z, A=A: z in A
        WA = W(Af, PL)
        t('E, F')
        if A != {x for x in WA if lt(x, K[i])}: f('E', i)
        if K[i] not in WA: f('F', i)
        # 4.40
        B = WWs[i + 1]; Bf = lambda z, B=B: z in B
        if not ag(A, PL): f('4.40 Ag', i)
        if K[i] not in B: f('4.40 Omega_{I+i} in WW_{i+1}', i)
        if A != {x for x in B if lt(x, K[i])}: f('4.40 WW_i = WW_{i+1} n Omega_{I+i}', i)
        # the step from i to i+1
        if not A <= B: f('step A c B', i)
        if not all(M(Bf, x) for x in B): f('step B c M(B)', i)
        WB = W(Bf, PL)
        if {x for x in WA if lt(x, K[i + 1])} != {x for x in WB if lt(x, K[i + 1])}: f('step 4.13(b)', i)
        # F(i+1) from E(i+1), K[i] in B: B+ n k' = B, k' in W(B+), so k' in W(B) (transfer at k')
        Ap = {y for z in B for y in WB if lt(y, Fn.plus(z))} | {Fn.plus(z) for z in B if Fn.plus(z) in PLs}
        t('step A+')
        if {y for y in Ap if lt(y, K[i + 1])} != B: f('step B+ n k\' = B', i)
        if K[i + 1] in PLs and K[i + 1] not in W(lambda z: z in Ap, PL): f('step ap-wup', i)
    # 4.41
    if OM1 not in WWs[0]: f('Omega_1 in WW_0')
    for n in range(3):
        if not Fn.inC(OM1, K[n], K[n]): f('InC', n)
        x = S(OM1, K[n])
        t('4.41')
        if x in PLs and x not in WWs[n + 1]: f('4.41 psi in WW_{n+1}', n)
        for y in PL:
            if lt(y, x):
                t('4.41 y')
                if y not in WWs[n + 1] or not lt(y, OM1): f('4.41 y', n, show(y))
    print(cnt); f.report('Section 4.7')

if __name__ == '__main__':
    {'lem': lem}[sys.argv[1]](int(sys.argv[2]))
