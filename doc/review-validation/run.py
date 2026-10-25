#!/usr/bin/env python3
"""Rerun current-checker validation; this does not reproduce historical variants."""
from pathlib import Path
import datetime
import hashlib
import json
import platform
import re
import subprocess
import time

root = Path(__file__).resolve().parents[2]
logdir = Path(__file__).resolve().parent

def output(*args):
    return subprocess.check_output(args, cwd=root, text=True).strip()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

seg = output('cabal', 'list-bin', 'exe:seg')
inputs = sorted(set(root.glob('src/*.hs')) | set(root.glob('app/*.hs')) |
                set(root.rglob('*.seg')) |
                {root / 'seg.cabal', root / 'cabal.project',
                 root / 'run-tests.sh', root / 'tests.expected'})
manifest = {
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'policy': 'split code identity and convertible dynamic arguments only; no branch or motive comparison',
    'checkout_base': output('git', 'rev-parse', 'HEAD'),
    'platform': platform.platform(),
    'ghc': output('ghc', '--numeric-version'),
    'cabal': output('cabal', '--numeric-version'),
    'build': 'cabal build exe:seg --offline (reported profile: ghc-9.6.7 -O1)',
    'binary': seg,
    'binary_sha256': digest(Path(seg)),
    'inputs_sha256': {str(p.relative_to(root)): digest(p) for p in inputs},
    'results': [],
}

def save():
    (logdir / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')

checks = [('regressions', ['./run-tests.sh'])] + [
    (name.replace('/', '-'), [seg, name + '/All.seg'])
    for name in ['core', 'sag/chatelet', 'sag/stone', 'sag/stoneseq',
                 'sag/cca', 'sag/ccacoh', 'sag/em']
]
save()
for label, command in checks:
    start = time.monotonic()
    logfile = logdir / (label + '.log')
    with logfile.open('w') as out:
        result = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    text = logfile.read_text()
    record = {'label': label, 'command': command, 'exit_code': result.returncode,
              'wall_seconds': round(time.monotonic() - start, 3), 'log': logfile.name}
    if label == 'regressions':
        record['matches_expected'] = text == (root / 'tests.expected').read_text()
    record['summaries'] = re.findall(r'^.*declarations.*$', text, re.MULTILINE)
    manifest['results'].append(record)
    save()
    print(json.dumps(record), flush=True)
manifest['input_changes_during_run'] = [str(p.relative_to(root)) for p in inputs
    if digest(p) != manifest['inputs_sha256'][str(p.relative_to(root))]]
save()
raise SystemExit(any(r['exit_code'] != 0 or r.get('matches_expected') is False
                     for r in manifest['results']) or bool(manifest['input_changes_during_run']))
