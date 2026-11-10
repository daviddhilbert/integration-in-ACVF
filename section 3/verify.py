#!/usr/bin/env python3
"""Build the Section 3 library and audit its current full types and axioms."""

from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.scratch' / 'section3-verified'
PREFIX = 'IntegrationInACVF.Section3.'
HEADLINES = [
    'GeneratesCompleteType.mem_iff',
    'generatesCompleteType_iff',
    'GeneratesCompleteType.subset',
    'GeneratesCompleteType.parameters_mono',
    'GeneratesCompleteType.inter_eq',
    'IsAtomic.eq_of_definable_subset',
    'IsAtomic.eq_or_disjoint',
    'GeneratesCompleteType.image',
    'IsAtomic.image_of_definable',
    'definable_image',
    'IsAtomic.image',
    'HasFiniteBallSupport.basic',
    'HasFiniteBallSupport.univ',
    'HasFiniteBallSupport.compl',
    'HasFiniteBallSupport.union',
    'HasFiniteBallSupport.inter',
    'hasFiniteBallSupport_of_boolean_closure',
    'IsLaminar.subset_of_splits',
    'IsLaminar.subsingleton_splitters',
    'splits_support',
    'finite_splitters',
    'finite_splitters_of_boolean_closure',
    'DefinableFamilies.isAlgebraicPoint_of_mem',
    'DefinableFamilies.definable_domain',
    'DefinableFamilies.definable_fibre',
    'DefinableFamilies.promote_fibre',
    'DefinableFamilies.IsAlgebraicPoint.map',
    'definable_range',
    'cutIndices_definable',
    'cutUnion_definable',
    'splits_cutUnion',
    'finite_cutIndices',
    'parametric_ball_atomic',
    'parametric_ball_atomic_of_code',
]
ACVF_HEADLINES = [
    'IntegrationInACVF.Section3ACVF.' + name for name in (
        'encodedBall_isKBall', 'encodedBalls_laminar', 'support_of_isBoolComb',
        'normalized_cMinimalOn', 'real_parametric_ball_atomic')
]
DEFINITIONS = [
    'GeneratesCompleteType', 'IsAtomic', 'Splits',
    'IsLaminar', 'HasFiniteBallSupport',
    'DefinableFamilies.IsAlgebraicPoint', 'CMinimalOn', 'cutIndices', 'cutUnion',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, log):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            encoding='utf-8', errors='replace')
    output = result.stdout + result.stderr
    (OUT / log).write_text(output, encoding='utf-8')
    print(output, end='')
    if result.returncode:
        raise RuntimeError(f'{command[0]} failed with exit {result.returncode}; see {log}')
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--acvf', action='store_true',
                        help='Also build and audit the actual ACVF bridge')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    status = OUT / 'status.txt'
    status.write_text('RUNNING\n', encoding='utf-8')
    try:
        sources = sorted((ROOT / 'section 3' / 'IntegrationSection3').glob('*.lean'))
        if args.acvf:
            sources += sorted((ROOT / 'section 3' / 'IntegrationSection3ACVF').glob('*.lean'))
        inputs = sources + [ROOT / name for name in (
            'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'section 3/verify.py')]
        before = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        target = 'IntegrationSection3ACVF' if args.acvf else 'IntegrationSection3'
        run(['lake', 'build', target], 'SectionBuild.log')
        compiler = run(['lake', 'env', 'lean', '--version'], 'Compiler.log').strip()
        names = [PREFIX + name for name in HEADLINES]
        if args.acvf:
            names += ACVF_HEADLINES
        audit = OUT / 'HeadlineAudit.lean'
        audit.write_text(
            ('import IntegrationSection3ACVF.Geometry\n' if args.acvf
             else 'import IntegrationSection3.Library\n')
            + 'set_option pp.explicit true\n'
            + '\n'.join('#print ' + PREFIX + name for name in DEFINITIONS)
            + '\n'
            + '\n'.join('#check @' + name + '\n#print axioms ' + name for name in names)
            + '\n', encoding='utf-8')
        output = run(['lake', 'env', 'lean', str(audit)], 'HeadlineAudit.log')
        if re.search(r'\berror\b|\bsorry(?:Ax)?\b', output, re.I):
            raise RuntimeError('Audit diagnostics contain an error or placeholder')
        audits = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
        audits += [(name, '') for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", output)]
        if len(audits) != len(names) or {name for name, _ in audits} != set(names):
            raise RuntimeError('Incomplete or unexpected axiom output')
        records = []
        for name, block in audits:
            axioms = {entry.strip() for entry in block.split(',') if entry.strip()}
            if axioms - ALLOWED:
                raise RuntimeError(f'Unexpected axioms for {name}: {sorted(axioms - ALLOWED)}')
            records.append({'name': name, 'axioms': sorted(axioms)})
        after = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        if before != after:
            raise RuntimeError('Sources or dependency pins changed during verification')
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
        receipt = {
            'checked_at_utc': datetime.now(timezone.utc).isoformat(),
            'compiler': compiler,
            'source_sha256': after,
            'dependencies': {p['name']: p['rev'] for p in manifest['packages']},
            'headline_audits': records,
            'audit_source_sha256': digest(audit),
            'audit_log_sha256': digest(OUT / 'HeadlineAudit.log'),
            'scope': ('Definition 3.1, first-order parametric atomicity, '
                      + ('and its actual ACVF real-index case; ' if args.acvf else '')
                      + 'full imaginary-parameter Lemma 3.2 remains open'),
            'build_scope': 'Incremental Lake Section 3 build plus freshly compiled headline audit',
        }
        (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
        status.write_text('PASS\n', encoding='utf-8')
        print(f'PASS: Section 3 library import and {len(records)} headline type/axiom checks.')
        return 0
    except Exception as exc:
        status.write_text('FAIL\n', encoding='utf-8')
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
