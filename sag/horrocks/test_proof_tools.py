#!/usr/bin/env python3
"""Regression checks for the untrusted ring generator, including SEG checking."""
import argparse
from pathlib import Path
import json
import re
import subprocess
import tempfile
import ring_normalise as rn


def spec(name, lhs, rhs, variables=('x', 'y', 'z')):
    return dict(name=name, variables=list(variables), left=lhs, right=rhs)


def closure(root):
    pending, files = ['All.seg'], {}
    while pending:
        name = pending.pop()
        if name in files: continue
        data = (root / name).read_bytes()
        files[name] = data
        text = re.sub(r'--[^\n]*', '', data.decode())
        pending += [s + '.seg' for s in re.findall(r'\bimport\s+([A-Za-z0-9_-]+)\s*;', text)]
    return files


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path, default=root.parent /
        'dist-newstyle/build/aarch64-osx/ghc-9.6.7/segd-0.1.0.0/x/segd/build/segd/segd')
    args = parser.parse_args()
    base = json.loads((root / 'ring_identities.json').read_text())
    assert rn.generate(base) == (root / 'GeneratedRing.seg').read_text(), 'regenerate GeneratedRing.seg'
    false = [('x+x', 'x'), ('x*x', 'y*y'), ('1', '0'), ('x-x', '1')]
    for lhs, rhs in false:
        try: rn.generate([spec('FalseIdentity', lhs, rhs)])
        except ValueError: pass
        else: raise AssertionError('accepted false identity: ' + lhs + ' = ' + rhs)
    for text in ['x/y', 'x**2', 'f(x)', 'undeclared', '33', 'True', 'x\n', '__import__("os")']:
        try: rn.generate([spec('Unsupported', text, text)])
        except (ValueError, SyntaxError): pass
        else: raise AssertionError('accepted unsupported syntax: ' + text)
    cases = [
        ('0', '0'), ('1', '1'), ('x+(-x)', '0'), ('(-x)+x', '0'),
        ('-(-x)', 'x'), ('(-x)*(-y)', 'x*y'),
        ('3*(x-y)+2*y', '3*x-y'),
        ('(x+y+z)*(x-y)', 'x*x-y*y+x*z-y*z'),
        ('(-(x+y))*z', '-x*z-y*z'), ('x+x+(-x)', 'x'),
        ('(x-y)*(y-x)', '2*x*y-x*x-y*y'), ('0*(x*y+z)', '0')]
    extra = [spec('Regression' + str(i), a, b) for i, (a, b) in enumerate(cases)]
    generated = rn.generate(base + extra)
    with tempfile.TemporaryDirectory(prefix='seg-proof-tools-') as tmp:
        target = Path(tmp)
        for name, data in closure(root).items(): (target / name).write_bytes(data)
        (target / 'GeneratedRing.seg').write_text(generated)
        result = subprocess.run([str(args.checker.resolve()), 'All.seg'], cwd=target,
                                capture_output=True, text=True, timeout=60)
        out = result.stdout + result.stderr
        assert result.returncode == 0 and '0 failed' in out and out.rstrip().endswith('OK'), out
        summary = re.search(r'All.seg: .*', out).group(0)
        print(f'{len(base)} production identities and twelve additional identities checked by SEG.')
        print(summary)
        # The checker must reject a damaged proof even though its claimed
        # ring identity is true. No trusted oracle is involved.
        bad, n = re.subn(r'(^  proof : .*?) = .*? ;$', r'\1 = refl Rg.z ;', generated,
                         count=1, flags=re.M)
        assert n == 1
        (target / 'GeneratedRing.seg').write_text(bad)
        result = subprocess.run([str(args.checker.resolve()), 'All.seg'], cwd=target,
                                capture_output=True, text=True, timeout=60)
        out = result.stdout + result.stderr
        assert 'FAILED: Theory.GeneratedRing.Four.proof' in out, out
    print('Four false identities and eight unsupported inputs rejected by the generator.')
    print('Deliberately corrupted generated proof rejected by SEG.')
    print('Deterministic regeneration matches the checked-in generated source.')


if __name__ == '__main__':
    main()
