#!/usr/bin/env python3
"""Generate ordinary SEG proofs of commutative-ring identities.

Input: JSON list of {name, variables, left, right}. Expressions use declared
variables, integer literals (absolute value <= 32), +, -, *, and parentheses.
No calls, division, hypotheses, or changes to SEG conversion are supported.
The generator is untrusted: generated .seg files must be checked by SEG.
"""
import argparse
import ast
from dataclasses import dataclass
import json
from pathlib import Path
import re


@dataclass(frozen=True)
class E:
    op: str
    args: tuple = ()

    def seg(self):
        if self.op == 'var':
            return 'v_' + self.args[0]
        if self.op in ('z', 'o'):
            return 'Rg.' + self.op
        return '(Rg.' + self.op + ' ' + ' '.join(a.seg() for a in self.args) + ')'


Z, O = E('z'), E('o')
def add(a, b): return E('add', (a, b))
def mul(a, b): return E('mul', (a, b))
def neg(a): return E('neg', (a,))
def mono(xs):
    if not xs: return O
    if len(xs) == 1: return E('var', (xs[0],))
    return mul(E('var', (xs[0],)), mono(xs[1:]))
def term(t):
    s, xs = t
    return mono(xs) if s == 1 else neg(mono(xs))
def poly(ts):
    return add(term(ts[0]), poly(ts[1:])) if ts else Z


def parse(text, variables):
    if len(text) > 2000 or '\n' in text or '\r' in text:
        raise ValueError('expected one expression line of at most 2000 characters')
    def go(t):
        if isinstance(t, ast.Name) and t.id in variables:
            return E('var', (t.id,))
        if isinstance(t, ast.Constant) and type(t.value) is int and 0 <= t.value <= 32:
            return integer(t.value)
        if isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.USub):
            return neg(go(t.operand))
        if isinstance(t, ast.BinOp):
            if isinstance(t.op, ast.Add): return add(go(t.left), go(t.right))
            if isinstance(t.op, ast.Mult): return mul(go(t.left), go(t.right))
            if isinstance(t.op, ast.Sub): return add(go(t.left), neg(go(t.right)))
        raise ValueError('unsupported expression or undeclared variable: ' + ast.dump(t))
    def integer(n):
        if n == 0: return Z
        if n == 1: return O
        return add(O, integer(n - 1))
    return go(ast.parse(text, mode='eval').body)


@dataclass(frozen=True)
class Proof:
    left: E
    right: E
    code: str


class Prover:
    def __init__(self):
        self.lines = []
        self.cache = {}

    def prove(self, a, b, code):
        if a == b: return Proof(a, b, '(refl ' + a.seg() + ')')
        if (a, b) in self.cache: return self.cache[a, b]
        if len(self.lines) >= 20000: raise ValueError('proof step limit exceeded')
        name = 'step' + str(len(self.lines))
        self.lines.append(f'  {name} : Id Rg.R {a.seg()} {b.seg()} = {code} ;')
        p = Proof(a, b, name)
        self.cache[a, b] = p
        return p

    def rule(self, name, args, a, b):
        return self.prove(a, b, '(' + name + ' ' + ' '.join(x.seg() for x in args) + ')')

    def refl(self, e): return self.prove(e, e, '')
    def sym(self, p): return self.prove(p.right, p.left, '(sym ' + p.code + ')')
    def chain(self, *ps):
        p = ps[0]
        for q in ps[1:]:
            if p.right != q.left: raise AssertionError(('broken chain', p, q))
            if p.left == p.right: p = q
            elif q.left != q.right:
                p = self.prove(p.left, q.right, f'(trans {p.code} {q.code})')
        return p
    def cong(self, op, *ps):
        a, b = E(op, tuple(p.left for p in ps)), E(op, tuple(p.right for p in ps))
        if len(ps) == 1: code = f'(ap Rg.{op} {ps[0].code})'
        else:
            p, q = ps
            code = f'(cong2 Rg.R Rg.{op} {p.left.seg()} {p.right.seg()} {q.left.seg()} {q.right.seg()} {p.code} {q.code})'
        return self.prove(a, b, code)

    def insert_factor(self, a, xs):
        v, m = mono((a,)), mono(xs)
        if not xs:
            return (a,), self.rule('Rg.mulO', [v], mul(v, O), v)
        if a <= xs[0]:
            return (a,) + xs, self.refl(mul(v, m))
        h, tail = mono(xs[:1]), mono(xs[1:])
        if len(xs) == 1:
            return xs + (a,), self.rule('Rg.mulC', [v, h], mul(v, h), mul(h, v))
        rest, p = self.insert_factor(a, xs[1:])
        swap = self.rule('RL[Rg].mul-swap', [v, h, tail], mul(v, m), mul(h, mul(v, tail)))
        return xs[:1] + rest, self.chain(swap, self.cong('mul', self.refl(h), p))

    def multiply_monomials(self, xs, ys):
        a, b = mono(xs), mono(ys)
        if not xs:
            return ys, self.rule('N.one-left', [b], mul(O, b), b)
        if not ys:
            return xs, self.rule('Rg.mulO', [a], mul(a, O), a)
        if len(xs) == 1: return self.insert_factor(xs[0], ys)
        h, tail = mono(xs[:1]), mono(xs[1:])
        zs, p = self.multiply_monomials(xs[1:], ys)
        ws, q = self.insert_factor(xs[0], zs)
        assoc = self.sym(self.rule('Rg.mulA', [h, tail, b], mul(h, mul(tail, b)), mul(a, b)))
        return ws, self.chain(assoc, self.cong('mul', self.refl(h), p), q)

    def multiply_terms(self, t, u):
        s, xs = t; r, ys = u
        a, b = mono(xs), mono(ys)
        zs, mp = self.multiply_monomials(xs, ys)
        if s == r == 1: return (1, zs), mp
        if s == 1:
            p = self.rule('RL[Rg].mul-neg', [a, b], mul(a, neg(b)), neg(mul(a, b)))
            return (-1, zs), self.chain(p, self.cong('neg', mp))
        p = self.rule('N.neg-mul-left', [a, term(u)], mul(neg(a), term(u)), neg(mul(a, term(u))))
        if r == 1: return (-1, zs), self.chain(p, self.cong('neg', mp))
        q = self.rule('RL[Rg].mul-neg', [a, b], mul(a, neg(b)), neg(mul(a, b)))
        nn = self.rule('N.neg-neg', [mul(a, b)], neg(neg(mul(a, b))), mul(a, b))
        return (1, zs), self.chain(p, self.cong('neg', q), nn, mp)

    def insert_term(self, t, ts):
        a = term(t)
        if not ts: return [t], self.refl(add(a, Z))
        u, rest = ts[0], ts[1:]
        b, c = term(u), poly(rest)
        if t[1] == u[1] and t[0] != u[0]:
            assoc = self.rule('Rg.addA', [a, b, c], add(a, add(b, c)), add(add(a, b), c))
            cancel = self.rule('Rg.addN' if t[0] == 1 else 'N.neg-cancel',
                               [mono(t[1])], add(a, b), Z)
            return rest, self.chain(assoc, self.cong('add', cancel, self.refl(c)),
                                    self.rule('RL[Rg].zl', [c], add(Z, c), c))
        if t[1] <= u[1]: return [t] + ts, self.refl(add(a, poly(ts)))
        rs, p = self.insert_term(t, rest)
        swap = self.rule('N.add-swap', [a, b, c], add(a, add(b, c)), add(b, add(a, c)))
        return [u] + rs, self.chain(swap, self.cong('add', self.refl(b), p))

    def add_polys(self, xs, ys):
        if not xs:
            return ys, self.rule('RL[Rg].zl', [poly(ys)], add(Z, poly(ys)), poly(ys))
        h, rest = term(xs[0]), poly(xs[1:])
        zs, p = self.add_polys(xs[1:], ys)
        ws, q = self.insert_term(xs[0], zs)
        assoc = self.sym(self.rule('Rg.addA', [h, rest, poly(ys)],
                                  add(h, add(rest, poly(ys))), add(poly(xs), poly(ys))))
        return ws, self.chain(assoc, self.cong('add', self.refl(h), p), q)

    def negate_poly(self, ts):
        if not ts: return [], self.rule('RL[Rg].neg-zero', [], neg(Z), Z)
        h, rest = term(ts[0]), poly(ts[1:])
        rs, p = self.negate_poly(ts[1:])
        t = (-ts[0][0], ts[0][1])
        q = self.refl(neg(h)) if ts[0][0] == 1 else self.rule('N.neg-neg', [mono(t[1])], neg(h), term(t))
        dist = self.rule('N.neg-add', [h, rest], neg(add(h, rest)), add(neg(h), neg(rest)))
        return [t] + rs, self.chain(dist, self.cong('add', q, p))

    def term_times_poly(self, t, ys):
        a = term(t)
        if not ys: return [], self.rule('RL[Rg].mul-zero', [a], mul(a, Z), Z)
        u, p = self.multiply_terms(t, ys[0])
        zs, q = self.term_times_poly(t, ys[1:])
        ws, r = self.insert_term(u, zs)
        dist = self.rule('Rg.dist', [a, term(ys[0]), poly(ys[1:])],
                         mul(a, poly(ys)), add(mul(a, term(ys[0])), mul(a, poly(ys[1:]))))
        return ws, self.chain(dist, self.cong('add', p, q), r)

    def multiply_polys(self, xs, ys):
        if not xs: return [], self.rule('RL[Rg].zero-mul', [poly(ys)], mul(Z, poly(ys)), Z)
        zs, p = self.term_times_poly(xs[0], ys)
        ws, q = self.multiply_polys(xs[1:], ys)
        rs, r = self.add_polys(zs, ws)
        dist = self.rule('N.dist-left', [term(xs[0]), poly(xs[1:]), poly(ys)],
                         mul(poly(xs), poly(ys)), add(mul(term(xs[0]), poly(ys)), mul(poly(xs[1:]), poly(ys))))
        return rs, self.chain(dist, self.cong('add', p, q), r)

    def normalise(self, e):
        if e == Z: return [], self.refl(Z)
        if e == O or e.op == 'var':
            ts = [(1, () if e == O else e.args)]
            return ts, self.sym(self.rule('Rg.addZ', [e], add(e, Z), e))
        xs, p = self.normalise(e.args[0])
        if e.op == 'neg':
            zs, q = self.negate_poly(xs)
            return zs, self.chain(self.cong('neg', p), q)
        ys, q = self.normalise(e.args[1])
        zs, r = (self.add_polys if e.op == 'add' else self.multiply_polys)(xs, ys)
        if len(zs) > 256: raise ValueError('normal form term limit exceeded')
        return zs, self.chain(self.cong(e.op, p, q), r)


def generate(specs):
    out = ['-- Generated by ring_normalise.py. Check this file with SEG.',
           '-- No solver result is trusted: every step is an ordinary equality proof.',
           'level l ; open Ring[l] ; open Presentations[l] ;']
    seen = set()
    for spec in specs:
        name, variables = spec['name'], spec['variables']
        if not re.fullmatch(r'[A-Z][A-Za-z0-9]*', name) or name in seen:
            raise ValueError('invalid or duplicate module name: ' + name)
        seen.add(name)
        if len(variables) != len(set(variables)) or any(not re.fullmatch(r'[a-z][a-z0-9_]*', v) for v in variables):
            raise ValueError('invalid or duplicate variables')
        left, right = parse(spec['left'], variables), parse(spec['right'], variables)
        prover = Prover()
        xs, p = prover.normalise(left); ys, q = prover.normalise(right)
        if xs != ys: raise ValueError(f'{name}: normal forms differ; identity not proved')
        proof = prover.chain(p, prover.sym(q))
        params = ' (Rg : CRing)' + (f" ({' '.join('v_' + v for v in variables)} : Rg.R)" if variables else '')
        out += [f'-- {spec["left"]} = {spec["right"]}', f'module {name}{params} {{',
                '  module N = RL[Rg] ;']
        out += prover.lines
        out += [f'  proof : Id Rg.R {left.seg()} {right.seg()} = {proof.code} ;', '} ;']
    return '\n'.join(out) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    try:
        text = generate(json.loads(args.input.read_text()))
    except (ValueError, SyntaxError, RecursionError) as e:
        parser.error(str(e))
    args.output.write_text(text)


if __name__ == '__main__':
    main()
