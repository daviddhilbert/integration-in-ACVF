#!/usr/bin/env python3
"""Require exact equality to the CI-passed proof inputs for a docs release.

The only permitted Lean-file difference is comments in the root import aggregate.
The release workflow separately checks the pinned revision's successful CI run.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
manifest = json.loads((ROOT / 'blueprint/proof-source-manifest.json').read_text())
rev = manifest['proof_revision']
inputs = list(manifest['sha256'])
subprocess.run(['git', 'diff', '--exit-code', rev, 'HEAD', '--', *inputs], cwd=ROOT, check=True)
for name, digest in manifest['sha256'].items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', rev], cwd=ROOT, text=True).splitlines()
proof_lean = {p for p in tracked if p.startswith('section ') and p.endswith('.lean')}
assert proof_lean == {p for p in inputs if p.endswith('.lean')}, 'Proof source inventory differs'
current_lean = {str(p.relative_to(ROOT)) for root in manifest['source_roots'] for p in (ROOT / root).rglob('*.lean')}
assert current_lean == proof_lean, 'Current proof source inventory differs'


def imports_only(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    assert all(re.fullmatch(r'import [A-Za-z0-9_.]+', line) for line in lines), 'Root aggregate contains non-import code'
    return lines


old = subprocess.check_output(['git', 'show', rev + ':IntegrationInACVF.lean'], cwd=ROOT, text=True)
assert imports_only(old) == imports_only((ROOT / 'IntegrationInACVF.lean').read_text()), 'Root imports changed'
print(json.dumps({'status': 'PASS', 'proof_revision': rev, 'proof_inputs': len(inputs), 'root_imports': 'unchanged'}))
