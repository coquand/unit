# Mirror of Setzer's Section 4.2 (C^a(A), tau^A(a), M(A)) for decidable classes A, and
# the tests of Lemma 5.5 (= Assumption 4.4), Lemma 4.7 and Lemma 4.9.
#   python3 otsec4.py agree N    C^a(A) by recursion on d = Def. 5.3/5.4 (K_a) split at the head
#   python3 otsec4.py split      4.9(e) fails for Setzer's last-summand split (A = {(e,1)})
#   python3 otsec4.py lem49e     4.9(e) for sums, any split: fails for both splits; holds when
#                                A n a~ is weakly downward closed (z =NF' x+y in A n a~ => x, y in A)
#   python3 otsec4.py lem47 N    Lemma 4.7 (a)-(h), both readings of b^{-1} in (g)
#   python3 otsec4.py lem49 N    Lemma 4.9 (a)-(e)
#   python3 otsec4.py ca47 N     the forms proved in CA.seg: (e) for every class and a in T'
#                                (no a in C_I(a), no A c M(A)); (f) with z = min{a, d}
#   python3 otsec4.py ca49e      4.9(e) for sums with "A n a~ weakly downward closed" in the
#                                class form: z in A n a~, z =NF' x + y => x, y in A n a~
# A class is a Python predicate on terms; "A n a" is {x in A | x <' a}.
import sys, itertools, functools
from otmirror import *
import otfun as Fn

ONE = Fn.ONE
OM1 = O(ONE)

def pool(N): return [x for n in range(1, N + 1) for x in terms(n) if isT(x) and isOT(x)]

# C^a(A) by recursion on d (the definition of CA.seg):
#   0, I: yes;  b+c (head/tail), phi_b c: d in A n a, or b, c in;  Omega_b: d in A n a, or b in;
#   psi_k c: if a <' k: d in A n a, or k, c in;  otherwise d in A n a.
def cin(a, A, d):
    k = d[0]
    own = A(d) and lt(d, a)
    if k in ('Z', 'I'): return True
    if k in ('P', 'F'): return own or (cin(a, A, d[1]) and cin(a, A, d[2]))
    if k == 'O': return own or cin(a, A, d[1])
    if lt(a, d[1]): return own or (cin(a, A, d[1]) and cin(a, A, d[2]))
    return own
def C(a, A, d): return isOT(d) and cin(a, A, d)

# Setzer's Def. 5.3/5.4: K_a(d) a set of finite sets; d in C^a(A) iff some L in K_a(d) is in A.
# Setzer splits a sum d =NF' b + c at its LAST summand c (Def. 2.11: c in A').  K below splits
# at the head, as cin does; Klast is Setzer's literal choice.  They differ: see split().
def K(a, d):
    if not (isOT(d) and isOT(a)): return set()
    k = d[0]
    single = {frozenset([d])} if lt(d, a) else set()        # {{d}} restricted to a
    def tensor(M, N): return {L | L2 for L in M for L2 in N}
    if k in ('Z', 'I'): return {frozenset()}
    if k in ('P', 'F'): return tensor(K(a, d[1]), K(a, d[2])) | single
    if k == 'O': return K(a, d[1]) | single
    if lt(a, d[1]): return tensor(K(a, d[1]), K(a, d[2])) | single
    return {frozenset([d])}
def CK(a, A, d): return isOT(d) and any(all(A(x) for x in L) for L in K(a, d))

def cinLast(a, A, d):
    k = d[0]; own = A(d) and lt(d, a)
    if k == 'P':
        xs = Fn.summands(d)
        return own or (cinLast(a, A, Fn.build(xs[:-1])) and cinLast(a, A, xs[-1]))
    if k in ('Z', 'I'): return True
    if k == 'F': return own or (cinLast(a, A, d[1]) and cinLast(a, A, d[2]))
    if k == 'O': return own or cinLast(a, A, d[1])
    if lt(a, d[1]): return own or (cinLast(a, A, d[1]) and cinLast(a, A, d[2]))
    return own

# Lemma 4.9(e) is stated for a =NF b + c with ANY split.  With Setzer's last-summand split it
# fails: e = psi_{Omega_1} 0, A = {(e, 1)} (A c M(A)), a = (Omega_1, e, 1) = Omega_1 + (e, 1),
# Omega_1 in M(A) \ a~, (e, 1) in A n a~, but a is not in M(A).  With the head/tail split it
# holds.  (Setzer's proof cites 4.4(c), which is for =NF' only; in his uses A is downward closed.)
def split(_=None):
    e = S(OM1, Z); c = P(e, ONE); d = P(OM1, c); A = lambda x: x == c
    for name, f in (('head', cin), ('last', cinLast)):
        Mf = lambda y: isOT(y) and f(y, A, y)
        print(name, ': A c M(A)', Mf(c), ' Omega_1 in M(A)\\a~', Mf(OM1) and not lt(OM1, Fn.tilde(d)),
              ' (e,1) in A n a~', A(c) and lt(c, Fn.tilde(d)), ' a in M(A) (4.9(e) says yes):', Mf(d))

def tau(a, A, y): return C(a, A, y) and lt(y, a)
def M(A, y): return isOT(y) and C(y, A, y)

# the classes tested: OT n e, and OT n e with one or two points removed; kept only if A c M(A)
def classes(P):
    es = [e for e in P if not isZero(e)][:: max(1, len(P) // 25)] + [I, O(Fn.suc(I))]
    out = [('empty', lambda x: False)]
    for e in es:
        out.append(('OT<' + show(e), lambda x, e=e: isOT(x) and lt(x, e)))
        below = [x for x in P if lt(x, e)]
        for g in below[1::max(1, len(below) // 3)][:3]:
            out.append(('OT<' + show(e) + '-' + show(g), lambda x, e=e, g=g: isOT(x) and lt(x, e) and x != g))
    return out
def goodClasses(P):
    return [(n, A) for (n, A) in classes(P) if all(M(A, x) for x in P if A(x))]

class Fails:
    def __init__(self): self.d = {}; self.n = 0
    def __call__(self, tag, *xs):
        self.d[tag] = self.d.get(tag, 0) + 1
        if self.d[tag] <= 3: print(tag, ' | '.join(show(x) if isinstance(x, tuple) else str(x) for x in xs))
    def report(self, name): print(name, 'failures', self.d or 'none')

def agree(N):
    P = pool(N); f = Fails(); cs = classes(P)
    for (n, A) in cs:
        for a in P:
            for d in P:
                if C(a, A, d) != CK(a, A, d): f('agree', n, a, d)
    print(len(cs), 'classes,', len(P), 'terms'); f.report('C by recursion = Def 5.4')

def mI(x): return Z if lt(x, I) else I

def lem47(N):
    P = pool(N); f = Fails(); cs = goodClasses(P)
    print(len(cs), 'classes with A c M(A) on the pool,', len(P), 'terms')
    CI = lambda a, x: Fn.inC(I, a, x)
    for (n, A) in cs:
        for a in P:
            at = Fn.tilde(a)
            for x in P:
                if C(a, A, x) != C(at, A, x): f('a', n, a, x)
                if A(x) and lt(x, a) and not C(a, A, x): f('h', n, a, x)
                if lt(a, OM1) and not C(a, A, x): f('d', n, a, x)
            for b in P:
                if le(a, b):
                    for x in P:
                        if C(b, A, x) and not C(a, A, x): f('b', n, a, b, x)
            # (f)
            for d in P:
                if d[0] == 'S' and lt(a, d[1]):
                    z = a if lt(a, d) else d
                    rhs = (A(d) and lt(d, at)) or (C(z, A, d[1]) and C(z, A, d[2]))
                    if C(a, A, d) != rhs: f('f', n, a, d)
        # (e)
        for a in P:
            if not CI(a, a): continue
            pa = S(I, a)
            if not isOT(pa): continue
            mids = [b for b in P if le(pa, b) and lt(b, I)]
            for b, c in itertools.product(mids, mids):
                for x in P:
                    if CI(a, x) and C(b, A, x) != C(c, A, x): f('e', n, a, b, c, x)
        # (g), reading b^{-1} as b^{-I}
        for b in P:
            bt = Fn.tilde(b); top = Fn.suc(bt)
            for c in P:
                if not le(bt, c): continue
                for x in P:
                    if lt(x, top) and C(b, A, x) != C(c, A, x):
                        f('g-I' if mI(b) == mI(c) else 'g-noside', n, b, c, x)
    f.report('Lemma 4.7')
    # (c): two classes agreeing below a~ give the same C^a
    for (n1, A1), (n2, A2) in itertools.combinations(cs, 2):
        for a in P[::3]:
            at = Fn.tilde(a)
            if all(A1(x) == A2(x) for x in P if lt(x, at)):
                for x in P:
                    if C(a, A1, x) != C(a, A2, x): f('c', n1, n2, a, x)
    f.report('Lemma 4.7 with (c)')

def lem49(N):
    P = pool(N); f = Fails(); cs = goodClasses(P)
    for (n, A) in cs:
        if not (M(A, Z) and M(A, I)): f('d', n)
        for a in P:
            at = Fn.tilde(a)
            for b in P:
                if le(b, a):
                    for y in P:
                        if tau(a, A, y) and lt(y, b) and not tau(b, A, y): f('a', n, a, b, y)
                    if Fn.tilde(b) == at:
                        for y in P:
                            if tau(b, A, y) != (tau(a, A, y) and lt(y, b)): f('b', n, a, b, y)
            if lt(a, OM1):
                for y in P:
                    if tau(a, A, y) != lt(y, a): f('c', n, a, y)
        # (e)
        ok = lambda x, at: (A(x) and lt(x, at)) or (M(A, x) and not lt(x, at))
        for a in P:
            if a[0] in ('P', 'F', 'O'):
                at = Fn.tilde(a)
                parts = [a[1]] if a[0] == 'O' else [a[1], a[2]]
                if all(ok(p, at) for p in parts) and not M(A, a): f('e', n, a)
    f.report('Lemma 4.9 (' + str(len(cs)) + ' classes, ' + str(len(P)) + ' terms)')

def initlast(z):
    xs = Fn.summands(z); return [Fn.build(xs[:-1]), xs[-1]] if z[0] == 'P' else []
def wclose(S):          # the closure of S under init/last of sums
    S = set(S); todo = list(S)
    while todo:
        for p in initlast(todo.pop()):
            if p not in S: S.add(p); todo.append(p)
    return S

def lem49e(_=None):
    import random
    atoms = [x for x in pool(5) if isA(x)] + [S(OM1, Z), S(OM1, ONE), O(Fn.suc(ONE)), S(O(Fn.suc(ONE)), Z)]
    atoms = sorted(set(atoms), key=lambda x: sum(lt(y, x) for y in atoms))
    sums = [t for n in (2, 3, 4) for xs in itertools.combinations_with_replacement(range(len(atoms)), n)
            for t in [Fn.build([atoms[i] for i in reversed(xs)])] if isOT(t)]
    e = S(OM1, Z)
    random.seed(3)
    POOL = atoms + random.sample(sums, 400) + [P(OM1, P(e, ONE)), P(OM1, P(e, P(ONE, ONE))), P(e, ONE)]
    seeds = [{P(e, ONE), ONE}, {P(e, ONE)}] + [set(random.sample(sums, 2)) | {ONE} for _ in range(300)]
    for dn, f in (('head', cin), ('last', cinLast)):
        Cf = lambda a, A, d: isOT(d) and f(a, A, d)
        Mf = lambda A, y: isOT(y) and Cf(y, A, y)
        fails = {'plain': 0, 'closed': 0}; tested = {'plain': 0, 'closed': 0}
        for S0 in seeds:
            for kind in ('plain', 'closed'):
                Sx = S0 if kind == 'plain' else wclose(S0)
                A = lambda x, Sx=Sx: x in Sx
                if not all(Mf(A, x) for x in Sx): continue
                for d in POOL:
                    if d[0] != 'P': continue
                    at = Fn.tilde(d)
                    if kind == 'closed' and not all(p in Sx for z in Sx if lt(z, at) for p in initlast(z)): continue
                    xs = Fn.summands(d)
                    ok = lambda y: (A(y) and lt(y, at)) or (Mf(A, y) and not lt(y, at))
                    for i in range(1, len(xs)):
                        b, c = Fn.build(xs[:i]), Fn.build(xs[i:])
                        if ok(b) and ok(c):
                            tested[kind] += 1
                            if not Mf(A, d): fails[kind] += 1
        print(dn, 'split: instances', tested, 'failures', fails)

def ca47(N):
    P = pool(N); f = Fails(); cs = classes(P); tested = {'e': 0, 'f': 0}
    TP = [x for n in range(1, N + 1) for x in terms(n) if isT(x)]
    for (n, A) in cs:
        for a in TP:
            pa = S(I, a)
            mids = [b for b in P if le(pa, b) and lt(b, I)]
            if not mids: continue
            for b, c in itertools.product(mids, mids):
                for x in P:
                    if Fn.inC(I, a, x):
                        tested['e'] += 1
                        if C(b, A, x) != C(c, A, x): f('e', n, a, b, c, x)
    for (n, A) in goodClasses(P):
        for a in P:
            at = Fn.tilde(a)
            for d in P:
                if d[0] == 'S' and lt(a, d[1]):
                    z = a if lt(a, d) else d
                    tested['f'] += 1
                    if C(a, A, d) != ((A(d) and lt(d, at)) or (C(z, A, d[1]) and C(z, A, d[2]))): f('f', n, a, d)
    print('instances', tested); f.report('CA.seg 4.7 (e), (f)')

def ca49e(_=None):
    import random
    atoms = [x for x in pool(5) if isA(x)] + [S(OM1, Z), S(OM1, ONE), O(Fn.suc(ONE)), S(O(Fn.suc(ONE)), Z)]
    atoms = sorted(set(atoms), key=lambda x: sum(lt(y, x) for y in atoms))
    sums = [t for n in (2, 3, 4) for xs in itertools.combinations_with_replacement(range(len(atoms)), n)
            for t in [Fn.build([atoms[i] for i in reversed(xs)])] if isOT(t)]
    random.seed(3)
    POOL = atoms + random.sample(sums, 400)
    seeds = [{P(S(OM1, Z), ONE), ONE}, {P(S(OM1, Z), ONE)}] + [set(random.sample(sums, 2)) | {ONE} for _ in range(300)]
    tested = 0; fails = 0
    for S0 in seeds:
        for Sx in (S0, wclose(S0)):
            A = lambda x, Sx=Sx: x in Sx
            if not all(M(A, x) for x in Sx): continue
            for d in POOL:
                if d[0] != 'P': continue
                at = Fn.tilde(d)
                B = lambda x: A(x) and lt(x, at)
                if not all(B(p) for z in Sx if B(z) for p in initlast(z)): continue
                xs = Fn.summands(d)
                ok = lambda y: B(y) or (M(A, y) and le(at, y))
                for i in range(1, len(xs)):
                    b, c = Fn.build(xs[:i]), Fn.build(xs[i:])
                    if ok(b) and ok(c):
                        tested += 1
                        if not M(A, d): fails += 1
    print('4.9(e) with WD(A n a~): instances', tested, 'failures', fails)

if __name__ == '__main__':
    {'agree': agree, 'lem47': lem47, 'lem49': lem49, 'split': split, 'lem49e': lem49e, 'ca47': ca47, 'ca49e': ca49e}[sys.argv[1]](int(sys.argv[2]) if len(sys.argv) > 2 else None)
