#!/usr/bin/env python3
"""Audit the imported QE boundary and run available sequel section verifiers.

Adapted from special-transformations/scripts/verify_ci.py at
9cc9760892092dd34cfad4a6dee655843c52f30c. Run with lake env python3.

--reuse-certified forwards the existing exact-receipt reuse option to the
Section 6 verifier. Every full type and permitted-axiom report is still
checked afresh; the default remains fresh compilation.
"""

import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
QE_HEADLINES = [
    'JohnsonACF.hasQEb',
    'hasQE_ACVF_val',
    'hasQEb_ACVF_val',
    'SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination',
    'ValPM.hasQE_ACVF_trivial_val',
    'ValPM.hasQEb_ACVF_trivial_val',
    'SpecialTransformations.TrivialRV.canonical_trivial_rv_qe',
    'SpecialTransformations.TrivialRV.hasQE',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def audit_foundation():
    out = ROOT / '.scratch' / 'ci-verified'
    headlines = QE_HEADLINES
    definitions = []
    print_options = 'set_option pp.explicit true\n'
    out.mkdir(parents=True, exist_ok=True)
    status = out / 'status.txt'
    status.write_text('RUNNING\n', encoding='utf-8')
    try:
        source = out / 'HeadlineAudit.lean'
        source.write_text(
            'import IntegrationInACVF\n'
            + print_options
            + '\n'.join('#print ' + name for name in definitions)
            + '\n'
            + '\n'.join('#check @' + h + '\n#print axioms ' + h for h in headlines)
            + '\n', encoding='utf-8')
        result = subprocess.run(
            ['lean', str(source)], cwd=ROOT, capture_output=True, text=True,
            encoding='utf-8', errors='replace')
        output = result.stdout + result.stderr
        (out / 'HeadlineAudit.log').write_text(output, encoding='utf-8')
        print(output, end='')
        if result.returncode or re.search(r'\berror\b|\bsorry(?:Ax)?\b', output, re.I):
            raise RuntimeError('Headline compilation or diagnostics failed')
        audits = re.findall(
            r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
        audits += [(name, '') for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", output)]
        if len(audits) != len(headlines) or {name for name, _ in audits} != set(headlines):
            raise RuntimeError('Incomplete or unexpected headline axiom audit')
        records = []
        for name, block in audits:
            axioms = {x.strip() for x in block.split(',') if x.strip()}
            if axioms - ALLOWED:
                raise RuntimeError('Unexpected axioms for ' + name + ': ' + str(axioms - ALLOWED))
            records.append({'name': name, 'axioms': sorted(axioms)})
        (out / 'headlines.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
        status.write_text('PASS\n', encoding='utf-8')
        print('PASS: inherited QE headline types and allowed axioms.')
    except Exception:
        status.write_text('FAIL\n', encoding='utf-8')
        raise



def main():
    out = ROOT / '.scratch' / 'ci-verified'
    out.mkdir(parents=True, exist_ok=True)
    outcomes = {}
    try:
        audit_foundation()
        outcomes['foundation'] = 'success'
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        outcomes['foundation'] = 'failure'

    for number in range(2, 8):
        verifier = ROOT / f'section {number}' / 'verify.py'
        label = f'section{number}'
        if not verifier.is_file():
            outcomes[label] = 'skipped'
            continue
        with (out / f'{label}.log').open('w', encoding='utf-8') as log:
            command = [sys.executable, str(verifier)]
            if number == 3:
                command.append('--acvf')
            if number == 6 and '--reuse-certified' in sys.argv:
                command.append('--reuse-certified')
            result = subprocess.run(
                command, cwd=ROOT,
                stdout=log, stderr=subprocess.STDOUT)
        outcomes[label] = 'success' if result.returncode == 0 else 'failure'

    (out / 'summary.json').write_text(
        json.dumps(outcomes, indent=2) + '\n', encoding='utf-8')
    output = os.environ.get('GITHUB_OUTPUT')
    if output:
        with Path(output).open('a', encoding='utf-8') as stream:
            for label, outcome in outcomes.items():
                stream.write(f'{label}={outcome}\n')
    for label, outcome in outcomes.items():
        print(f'{label}: {outcome}')
    return int('failure' in outcomes.values())


if __name__ == '__main__':
    raise SystemExit(main())
