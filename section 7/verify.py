#!/usr/bin/env python3
"""Check the curated Section 7 reconstruction boundary, not full coverage."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
SECTION = ROOT / 'section 7'
OUT = ROOT / '.scratch/section7-verified'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    registry = json.loads((SECTION / 'VERIFICATION.json').read_text())
    for relative, expected in registry['source_sha256'].items():
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f'Source differs from the reviewed checkpoint: {relative}')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    revisions = {p['name']: p['rev'] for p in manifest['packages']}
    for name, expected in registry['dependency_pins'].items():
        if revisions.get(name) != expected:
            raise RuntimeError(f'Dependency pin differs from the reviewed checkpoint: {name}')
    if (ROOT / 'lean-toolchain').read_text().strip() != registry['lean_toolchain']:
        raise RuntimeError('Lean toolchain differs from the reviewed checkpoint')
    OUT.mkdir(parents=True, exist_ok=True)
    subprocess.run(['lake', 'build', '+Integration7.Library'], cwd=ROOT, check=True)
    names = registry['declarations']
    if len(names) != len(set(names)):
        raise RuntimeError('Duplicate audit entries')
    source = OUT / 'HeadlineAudit.lean'
    source.write_text('''import Integration7.Library
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry IntegrationInACVF.Section7
set_option pp.universes true
set_option pp.proofs false
''' + '\n'.join('#check @' + name + '\n#print axioms ' + name for name in names) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(source)], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = OUT / 'HeadlineAudit.log'
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f'Lean audit failed; see {log}')
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout, re.S)
    if {name for name, _ in reports} != set(names) or len(reports) != len(names):
        raise RuntimeError('Missing or unexpected axiom reports')
    for name, body in reports:
        axioms = {re.sub(r'\.\{[^}]*\}', '', item.strip()) for item in body.split(',') if item.strip()}
        if not axioms <= ALLOWED:
            raise RuntimeError(f'Unapproved axioms for {name}: {sorted(axioms - ALLOWED)}')
    receipt = {'status': 'PASS', 'scope': registry['scope'], 'exports': len(names),
               'source_sha256': registry['source_sha256'], 'audit_log': str(log.relative_to(ROOT))}
    (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'PASS: {len(names)} Section 7 reconstruction exports; full section remains incomplete.')


if __name__ == '__main__':
    main()
