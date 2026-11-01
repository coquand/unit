# Generates the dispatcher lt-trans at the end of OTTrans.seg: transitivity of <'
# by recursion on x, then y, then z, one case per triple of constructors.
#   python3 gentrans.py              rewrites OTTrans.seg after its marker line
#   python3 gentrans.py -             prints the generated block
# Each case calls one lemma of OTTrans.seg; see the comment at the top of that file.
CONS = ['zero', 'plus', 'phi', 'psi', 'om', 'ii']
ARGS = {'zero': [], 'plus': ['0', 's'], 'phi': ['0', '1'], 'psi': ['0', '1'], 'om': ['0'], 'ii': []}
IH = {'x': 'r', 'y': 's', 'z': 't'}
TTSUB = {('plus', 0): 'isT-plus0', ('plus', 1): 'isT-plusS', ('phi', 0): 'isT-phi0', ('phi', 1): 'isT-phi1',
         ('psi', 0): 'isT-psi0', ('psi', 1): 'isT-psi1', ('om', 0): 'isT-om0'}

class Pos:
    def __init__(self, v, k):
        self.v, self.k = v, k
        self.sub = [v + a for a in ARGS[k]]
        self.ih = [IH[v] + a for a in ARGS[k]]
        self.term = k if not self.sub else '(' + ' '.join([k] + self.sub) + ')'
        self.tt = 't' + v
    def ttsub(self, i):
        return '(' + ' '.join([TTSUB[(self.k, i)]] + self.sub + [self.tt]) + ')'

def ih(p, i, x, y, z, rest):
    # the induction hypothesis at sub-term i of position p; rest = the later components
    if p.v == 'x':
        (y1, ty1), (z1, tz1) = rest
        return '(%s %s %s %s %s %s)' % (p.ih[i], y1, z1, p.ttsub(i), ty1, tz1)
    if p.v == 'y':
        ((z1, tz1),) = rest
        return '(%s %s tx %s %s)' % (p.ih[i], z1, p.ttsub(i), tz1)
    return '(%s tx ty %s)' % (p.ih[i], p.ttsub(i))

def kT(txy, tyz, txz, last):
    if txy == 'false': return '(\\ e1 e2 p q -> abF p)'
    if tyz == 'false': return '(\\ e1 e2 p q -> abF q)'
    if txz == 'true': return '(\\ e1 e2 p q -> refl true)'
    return '(\\ e1 e2 p q -> %s p q)' % last

def lex(x, y, z, key, tag, view, tt_key, small, last):
    # the lexicographic step; small(p) says that the key of p is a proper sub-term
    ps = [x, y, z]
    hk = [key(p) for p in ps]
    tk = [tt_key(p) for p in ps]
    first = next(p for p in ps if small(p))
    if first is x: kH = ih(x, 0, x, y, z, [(hk[1], tk[1]), (hk[2], tk[2])])
    elif first is y: kH = ih(y, 0, x, y, z, [(hk[2], tk[2])])
    else: kH = ih(z, 0, x, y, z, [])
    txy, tyz, txz = tag(x, y), tag(y, z), tag(x, z)
    return 'by-lex %s %s %s %s %s %s %s %s %s %s %s %s %s %s h1 h2' % (
        x.term, y.term, z.term, hk[0], hk[1], hk[2], txy, tyz, txz,
        view(x, y), view(y, z), view(x, z), kH, kT(txy, tyz, txz, last))

# sums
def sumcase(x, y, z):
    P = lambda p: p.k == 'plus'
    key = lambda p: p.sub[0] if P(p) else p.term
    ttk = lambda p: p.ttsub(0) if P(p) else p.tt
    def tag(u, v):
        if P(u) and P(v): return '(lt %s %s)' % (u.sub[1], v.sub[1])
        return 'true' if (P(v) and not P(u)) else 'false'
    def view(u, v):
        if P(u) and P(v): return '(lex-PP %s %s %s %s)' % (u.sub[0], u.sub[1], v.sub[0], v.sub[1])
        if P(u): return '(lex-PA %s %s %s (refl true))' % (u.sub[0], u.sub[1], v.term)
        if P(v): return '(lex-AP %s (refl true) %s %s)' % (u.term, v.sub[0], v.sub[1])
        return '(lex-self %s %s)' % (u.term, v.term)
    last = '(rs ys zs %s %s %s)' % (x.ttsub(1), y.ttsub(1), z.ttsub(1)) if (P(x) and P(y) and P(z)) else None
    return lex(x, y, z, key, tag, view, ttk, P, last)

def phicase(x, y, z):
    F = lambda p: p.k == 'phi'
    g = '(refl true)'
    a, b = x.sub if F(x) else (None, None)
    c, d = y.sub if F(y) else (None, None)
    e, f = z.sub if F(z) else (None, None)
    X, Y, Z = x.term, y.term, z.term
    pat = ''.join('F' if F(p) else 'G' for p in (x, y, z))
    if pat == 'FFF':
        return 'caseFFF %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s h1 h2' % (
            a, b, c, d, e, f, x.ttsub(0), y.ttsub(0), z.ttsub(0),
            ih(x, 0, x, y, z, [(c, y.ttsub(0)), (e, z.ttsub(0))]),
            ih(x, 0, x, y, z, [(e, z.ttsub(0)), (c, y.ttsub(0))]),
            ih(x, 1, x, y, z, [(Y, 'ty'), (Z, 'tz')]),
            ih(x, 1, x, y, z, [(Y, 'ty'), (f, z.ttsub(1))]),
            ih(x, 1, x, y, z, [(d, y.ttsub(1)), (Z, 'tz')]),
            ih(x, 1, x, y, z, [(d, y.ttsub(1)), (f, z.ttsub(1))]),
            ih(z, 1, x, y, z, []),
            ih(y, 1, x, y, z, [(Z, 'tz')]),
            ih(y, 1, x, y, z, [(f, z.ttsub(1))]))
    if pat == 'FFG':
        return 'caseFFG %s %s %s %s %s %s %s %s %s %s h1 h2' % (
            a, b, c, d, Z, g,
            ih(x, 0, x, y, z, [(c, y.ttsub(0)), (Z, 'tz')]),
            ih(x, 1, x, y, z, [(Y, 'ty'), (Z, 'tz')]),
            ih(x, 1, x, y, z, [(d, y.ttsub(1)), (Z, 'tz')]),
            ih(y, 1, x, y, z, [(Z, 'tz')]))
    if pat == 'FGF':
        return 'caseFGF %s %s %s %s %s %s ty %s %s %s %s %s %s %s h1 h2' % (
            a, b, Y, e, f, x.ttsub(0), z.ttsub(0), z.ttsub(1), g,
            ih(x, 0, x, y, z, [(Y, 'ty'), (e, z.ttsub(0))]),
            ih(x, 1, x, y, z, [(Y, 'ty'), (Z, 'tz')]),
            ih(x, 1, x, y, z, [(Y, 'ty'), (f, z.ttsub(1))]),
            ih(z, 1, x, y, z, []))
    if pat == 'GFF':
        return 'caseGFF %s %s %s %s %s tx %s %s %s %s %s %s %s %s %s h1 h2' % (
            X, c, d, e, f, y.ttsub(0), y.ttsub(1), z.ttsub(0), z.ttsub(1), g,
            ih(y, 0, x, y, z, [(e, z.ttsub(0))]),
            ih(y, 1, x, y, z, [(Z, 'tz')]),
            ih(y, 1, x, y, z, [(f, z.ttsub(1))]),
            ih(z, 1, x, y, z, []))
    if pat == 'FGG':
        return 'caseFGG %s %s %s %s %s %s %s %s h1 h2' % (
            a, b, Y, Z, g, g,
            ih(x, 0, x, y, z, [(Y, 'ty'), (Z, 'tz')]),
            ih(x, 1, x, y, z, [(Y, 'ty'), (Z, 'tz')]))
    if pat == 'GFG':
        return 'caseGFG %s %s %s %s tx %s %s %s %s %s %s h1 h2' % (
            X, c, d, Z, y.ttsub(0), y.ttsub(1), g, g,
            ih(y, 0, x, y, z, [(Z, 'tz')]),
            ih(y, 1, x, y, z, [(Z, 'tz')]))
    if pat == 'GGF':
        return 'caseGGF %s %s %s %s tx ty %s %s %s %s %s %s h1 h2' % (
            X, Y, e, f, z.ttsub(0), z.ttsub(1), g, g,
            ih(z, 0, x, y, z, []),
            ih(z, 1, x, y, z, []))
    raise Exception(pat)

# G': kinds S (psi, index /= I), T (psi, index I), O, I
def gcase(x, y, z, kinds):
    kd = dict(zip('xyz', kinds))
    K = lambda p: kd[p.v]
    hi = lambda p: 'hi' + p.v
    if 'S' in kinds:
        S = lambda p: K(p) == 'S'
        key = lambda p: p.sub[0] if S(p) else p.term
        ttk = lambda p: p.ttsub(0) if S(p) else p.tt
        def tag(u, v):
            if S(u) and S(v): return '(lt %s %s)' % (u.sub[1], v.sub[1])
            return 'true' if (S(u) and not S(v)) else 'false'
        def view(u, v):
            ku, kv = K(u), K(v)
            if ku == 'S' and kv == 'S': return '(lex-SS %s %s %s %s %s %s)' % (u.sub[0], u.sub[1], v.sub[0], v.sub[1], hi(u), hi(v))
            if ku == 'S' and kv == 'T': return '(lex-ST %s %s %s %s %s %s %s)' % (u.sub[0], u.sub[1], v.sub[0], v.sub[1], u.tt, hi(u), hi(v))
            if ku == 'S' and kv == 'O': return '(lex-SO %s %s %s %s)' % (u.sub[0], u.sub[1], v.sub[0], hi(u))
            if ku == 'S' and kv == 'I': return '(lex-SI %s %s %s)' % (u.sub[0], u.sub[1], hi(u))
            if ku == 'T' and kv == 'S': return '(lex-TS %s %s %s %s %s %s)' % (u.sub[0], u.sub[1], v.sub[0], v.sub[1], hi(u), hi(v))
            if ku == 'O' and kv == 'S': return '(lex-OS %s %s %s %s %s %s)' % (u.sub[0], v.sub[0], v.sub[1], u.tt, v.ttsub(0), hi(v))
            if ku == 'I' and kv == 'S': return '(lex-IS %s %s %s %s)' % (v.sub[0], v.sub[1], v.ttsub(0), hi(v))
            return '(lex-self %s %s)' % (u.term, v.term)
        last = '(r1 y1 z1 %s %s %s)' % (x.ttsub(1), y.ttsub(1), z.ttsub(1)) if kinds == 'SSS' else None
        return lex(x, y, z, key, tag, view, ttk, S, last)
    if 'O' in kinds:
        O = lambda p: K(p) == 'O'
        key = lambda p: p.sub[0] if O(p) else p.term
        ttk = lambda p: p.ttsub(0) if O(p) else p.tt
        tag = lambda u, v: 'true' if (O(v) and not O(u)) else 'false'
        def view(u, v):
            ku, kv = K(u), K(v)
            if ku == 'O' and kv == 'O': return '(lex-OO %s %s)' % (u.sub[0], v.sub[0])
            if ku == 'O' and kv == 'I': return '(lex-OI %s)' % u.sub[0]
            if ku == 'O' and kv == 'T': return '(lex-OT %s %s %s %s %s %s)' % (u.sub[0], v.sub[0], v.sub[1], u.ttsub(0), v.tt, hi(v))
            if ku == 'I' and kv == 'O': return '(lex-IO %s %s)' % (v.sub[0], v.ttsub(0))
            if ku == 'T' and kv == 'O': return '(lex-TO %s %s %s %s)' % (u.sub[0], u.sub[1], v.sub[0], hi(u))
            return '(lex-self %s %s)' % (u.term, v.term)
        return lex(x, y, z, key, tag, view, ttk, O, None)
    # Fi'
    if kinds == 'TTT':
        return 'caseTTT x0 x1 y0 y1 z0 z1 hix hiy hiz (r1 y1 z1 %s %s %s) h1 h2' % (x.ttsub(1), y.ttsub(1), z.ttsub(1))
    if kinds == 'TTI': return 'lt-TI x0 x1 hix'
    if kinds[1] == 'I': return 'abF h2' if kinds[2] == 'I' else 'abF (trans (sym (lt-IT z0 z1 hiz)) h2)'
    return 'abF h1' if kinds[1] == 'I' else 'abF (trans (sym (lt-IT y0 y1 hiy)) h1)'

def gsplit(x, y, z, todo, kinds, ind):
    # split the index of each psi into I (T) and not I (S)
    if not todo:
        return gcase(x, y, z, kinds)
    p, rest = todo[0], todo[1:]
    if p.k != 'psi':
        return gsplit(x, y, z, rest, kinds + ('O' if p.k == 'om' else 'I'), ind)
    pad = '\n' + ' ' * (ind + 2)
    return ('boolCases (LT %s %s) (isI %s)%s(\\ hi%s -> %s)%s(\\ hi%s -> %s)' % (
        x.term, z.term, p.sub[0],
        pad, p.v, gsplit(x, y, z, rest, kinds + 'T', ind + 2),
        pad, p.v, gsplit(x, y, z, rest, kinds + 'S', ind + 2)))

def leaf(kx, ky, kz):
    x, y, z = Pos('x', kx), Pos('y', ky), Pos('z', kz)
    ks = (kx, ky, kz)
    if kz == 'zero': return 'abF h2'
    if ky == 'zero': return 'abF h1'
    if kx == 'zero': return 'refl true'
    if 'plus' in ks: return sumcase(x, y, z)
    if 'phi' in ks: return phicase(x, y, z)
    return gsplit(x, y, z, [x, y, z], '', 6)

def pat(v, k):
    p = Pos(v, k)
    if not p.sub: return k
    return '%s %s | %s' % (k, ' '.join(p.sub), ' '.join(p.ih))

def main():
    out = []
    out.append('lt-trans : (x y z : T) -> TT x -> TT y -> TT z -> LT x y -> LT y z -> LT x z = split {')
    for i, kx in enumerate(CONS):
        out.append('  %s -> split {' % pat('x', kx))
        for j, ky in enumerate(CONS):
            out.append('    %s -> split {' % pat('y', ky))
            for k, kz in enumerate(CONS):
                sep = ' ;' if k < len(CONS) - 1 else ''
                out.append('      %s -> \\ tx ty tz h1 h2 ->\n        %s%s' % (pat('z', kz), leaf(kx, ky, kz), sep))
            out.append('    }' + (' ;' if j < len(CONS) - 1 else ''))
        out.append('  }' + (' ;' if i < len(CONS) - 1 else ''))
    out.append('} ;')
    return '\n'.join(out) + '\n'

MARK = '-- Transitivity (generated by tools/gentrans.py)\n'

if __name__ == '__main__':
    import sys, os
    block = main()
    if sys.argv[1:] == ['-']:
        sys.stdout.write(block)
    else:
        f = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'OTTrans.seg')
        src = open(f).read()
        i = src.index(MARK) + len(MARK)
        open(f, 'w').write(src[:i] + '\n' + block)
