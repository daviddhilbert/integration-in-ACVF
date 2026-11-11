#!/usr/bin/env python3
"""Compile and inspect the sequel's Section 5 proof batch."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.scratch' / 'section5-verified'
HEADLINES = [
    'IntegrationInACVF.Section5.lemma_5_1_real_base',
    'IntegrationInACVF.Section5.gamma_identity_graph',
    'IntegrationInACVF.Section5.gamma_composition_graph',
    'IntegrationInACVF.Section5.lemma_5_1_gamma_presented',
    'IntegrationInACVF.Section5.common_gamma_presentation',
    'IntegrationInACVF.Section5.lemma_5_1',
    'IntegrationInACVF.Section5.toKeyImage_surjective',
    'IntegrationInACVF.Section5.contraction_surjective',
    'IntegrationInACVF.Section5.contraction_injective_iff',
    'IntegrationInACVF.Section5.contraction_bijective_iff',
    'IntegrationInACVF.Section5.exists_unique_bijective_contraction',
    'IntegrationInACVF.Section5.UnaryRelative',
    'IntegrationInACVF.Section5.RelativelyUnary',
    'IntegrationInACVF.Section5.unaryRelative_id',
    'IntegrationInACVF.Section5.unaryRelative_comp',
    'IntegrationInACVF.Section5.unaryRelative_inverse',
    'IntegrationInACVF.Section5.relativelyUnary_inverse',
    'IntegrationInACVF.Section5.unaryRelative_one',
    'IntegrationInACVF.Section5.canonical_unaryRelative',
]

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, name):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            encoding='utf-8', errors='replace')
    output = result.stdout + result.stderr
    (OUT / name).write_text(output, encoding='utf-8')
    print(output, end='')
    if result.returncode:
        raise RuntimeError(f'{command[0]} exited {result.returncode}; see {name}')
    return output


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    status = OUT / 'status.txt'
    status.write_text('RUNNING\n', encoding='utf-8')
    try:
        sources = sorted((ROOT / 'section 5' / 'IntegrationSection5').glob('*.lean'))
        inputs = sources + [ROOT / p for p in (
            'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'section 5/verify.py')]
        before = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        run(['python3', 'scripts/prepare_ci.py'], 'DependencyPins.log')
        run(['lake', 'build', 'IntegrationSection5'], 'SectionBuild.log')
        compiler = run(['lake', 'env', 'lean', '--version'], 'Compiler.log').strip()
        audit = OUT / 'HeadlineAudit.lean'
        audit.write_text('import IntegrationSection5.Library\n'
                         'set_option pp.explicit true\n'
                         'set_option pp.universes true\n'
                         'set_option pp.fullNames true\n'
                         '#print IntegrationInACVF.Section5.UnaryRelative\n'
                         '#print IntegrationInACVF.Section5.RelativelyUnary\n'
                         + '\n'.join('#check @' + name + '\n#print axioms ' + name
                                     for name in HEADLINES) + '\n', encoding='utf-8')
        output = run(['lake', 'env', 'lean', str(audit)], 'HeadlineAudit.log')
        if re.search(r'\berror\b|\bsorry(?:Ax)?\b', output, re.I):
            raise RuntimeError('Headline diagnostics failed')
        audits = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
        audits += [(name, '') for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", output)]
        if len(audits) != len(HEADLINES) or {name for name, _ in audits} != set(HEADLINES):
            raise RuntimeError('Incomplete or unexpected axiom output')
        records = []
        for name, block in audits:
            axioms = {a.strip() for a in block.split(',') if a.strip()}
            if axioms - ALLOWED:
                raise RuntimeError('Unexpected axioms for ' + name)
            records.append({'name': name, 'axioms': sorted(axioms)})
        after = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        if before != after:
            raise RuntimeError('Source or pin identity changed during verification')
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
        receipt = {
            'checked_at_utc': datetime.now(timezone.utc).isoformat(),
            'compiler': compiler,
            'source_sha256': after,
            'dependencies': {p['name']: p['rev'] for p in manifest['packages']},
            'headline_audits': records,
            'complete_type_and_axiom_output': output,
            'audit_source_sha256': digest(audit),
            'audit_log_sha256': digest(OUT / 'HeadlineAudit.log'),
            'scope': 'Lemma 5.1 over real and original Gamma bases; quotient and relatively unary calculus. See STATUS.md for the exact scope; not a proof of Lemma 5.2.',
            'build_scope': 'Incremental Lake Section 5 build and fresh full-type/axiom audit',
        }
        (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
        status.write_text('PASS\n', encoding='utf-8')
        print('PASS: Section 5 proof batch; 19 complete type/axiom audits.')
        return 0
    except Exception as exc:
        status.write_text('FAIL\n', encoding='utf-8')
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
