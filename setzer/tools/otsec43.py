# Mirror of Setzer's Section 4.3: W(A) (Assumption 4.10 = Def. 5.6) and Lemma 4.13,
# on a finite pool P of OT.  W(A) is the least S c P with
#     x in M(A), tau^A(x) n P c S  =>  x in S
# (the inductive definition restricted to P: a test, not the infinite set).
#   python3 otsec43.py tilde N   y, a in OT, y <' Omega_{a+1} => y~ <=' Omega_a     (tilde-bound)
#   python3 otsec43.py lem413 N  Lemma 4.13 (a), (b), (c), (d) and the core lemma (wa-agree)
import sys
from otmirror import *
import otfun as Fn
from otsec4 import pool, tau, M, classes, goodClasses, Fails, OM1

def W(A, P):
    S = set()
    while True:
        new = {x for x in P if x not in S and M(A, x) and all(y in S for y in P if tau(x, A, y))}
        if not new: return S
        S |= new

def tilde(N):
    P = pool(N); f = Fails(); n = 0
    for a in P:
        oa1 = Fn.omF(Fn.suc(a)); oa = Fn.omF(a)
        for y in P:
            if lt(y, oa1):
                n += 1
                if not le(Fn.tilde(y), oa): f('tilde', a, y)
    print(n, 'pairs'); f.report('y <\' Omega_{a+1} => y~ <=\' Omega_a')

def lem413(N):
    P = pool(N); f = Fails(); cs = goodClasses(P)
    Ws = {n: W(A, P) for (n, A) in cs}
    for (n, A) in cs:
        S = Ws[n]
        for x in S:                                          # (a)
            if not M(A, x): f('a-M', n, x)
            for y in P:
                if tau(x, A, y) and y not in S: f('a-tau', n, x, y)
        for x in S:                                          # (d): W(A) n Omega_1 is a segment of OT
            if lt(x, OM1):
                for z in P:
                    if le(z, x) and z not in S: f('d', n, x, z)
    m = 0
    for (n, A) in cs:                                        # (b), (c)
        for (k, B) in cs:
            for a in P:
                oa = Fn.omF(a); oa1 = Fn.omF(Fn.suc(a))
                if all(A(x) == B(x) for x in P if lt(x, oa)):
                    m += 1
                    for x in P:
                        if lt(x, oa1):
                            if M(A, x) != M(B, x): f('b-M', n, k, a, x)
                            if (x in Ws[n]) != (x in Ws[k]): f('b-W', n, k, a, x)
            if all(A(x) == B(x) for x in P) and Ws[n] != Ws[k]: f('c', n, k)
    print(len(cs), 'classes,', len(P), 'terms,', m, 'triples for (b),', sum(len(s) for s in Ws.values()), 'points of W')
    f.report('Lemma 4.13')

if __name__ == '__main__':
    {'tilde': tilde, 'lem413': lem413}[sys.argv[1]](int(sys.argv[2]))
