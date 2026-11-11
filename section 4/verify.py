#!/usr/bin/env python3
"""Build and audit Section 4's actual declarations in the pinned project.

Use --descent-only for the generic supporting theorem batch. That selected
check does not certify Lemma 4.1 or any ACVF integration result.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
GENERIC = [
    'representative_spec', 'descendFun_spec', 'descendMap', 'descendMap_spec', 'descendMap_unique',
]
TRANSLATIONS = [
    'inverse_sub', 'displacementMap_apply', 'displacement_constant',
    'offsetMap', 'offsetMap_spec', 'inverse_fibre_translate', 'lemma_4_1_real_base',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--descent-only', action='store_true')
    args = parser.parse_args()
    selected = args.descent_only
    out = ROOT / '.scratch' / ('section4-descent-verified' if selected else 'section4-verified')
    out.mkdir(parents=True, exist_ok=True)
    status = out / 'status.txt'
    status.write_text('RUNNING\n')

    def run(command, filename):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                encoding='utf-8', errors='replace')
        output = result.stdout + result.stderr
        (out / filename).write_text(output, encoding='utf-8')
        print(output, end='')
        if result.returncode:
            raise RuntimeError(f'{command[0]} exited {result.returncode}; see {filename}')
        return output

    try:
        module = 'IntegrationSection4.DefinableDescent' if selected else 'IntegrationSection4.Library'
        sources = [ROOT / 'section 4/IntegrationSection4/DefinableDescent.lean'] if selected else sorted(
            (ROOT / 'section 4/IntegrationSection4').glob('*.lean'))
        inputs = sources + [ROOT / p for p in (
            'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'section 4/verify.py')]
        before = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        run(['lake', 'build', module], 'SectionBuild.log')
        compiler = run(['lake', 'env', 'lean', '--version'], 'Compiler.log').strip()
        names = ['IntegrationInACVF.Section4.DefinableDescent.' + name for name in GENERIC]
        if not selected:
            names = []
            for source in sources:
                content = source.read_text()
                namespaces = []
                for line in content.splitlines():
                    ns = re.match(r'^namespace (\S+)', line)
                    if ns:
                        namespaces.append(ns[1])
                    elif re.match(r'^end(?: |$)', line) and namespaces:
                        namespaces.pop()
                    else:
                        theorem = re.match(r'^(?:noncomputable )?(?:theorem|def) (\S+)', line)
                        if theorem:
                            names.append('.'.join(namespaces + [theorem[1]]))
            names += ['IntegrationInACVF.Section4.DefinableDescent.descendMap',
                      'IntegrationInACVF.Section4.TranslationOffsets.offsetMap']
        names = list(dict.fromkeys(names))
        audit = out / 'HeadlineAudit.lean'
        audit.write_text(f'import {module}\n'
                         'set_option pp.explicit true\n'
                         'set_option pp.universes false\n'
                         'set_option pp.fullNames true\n'
                         'set_option format.width 120\n'
                         + '\n'.join('#check @' + name + '\n#print axioms ' + name for name in names)
                         + '\n', encoding='utf-8')
        output = run(['lake', 'env', 'lean', str(audit)], 'HeadlineAudit.log')
        if re.search(r'\berror\b|\bsorry(?:Ax)?\b', output, re.I):
            raise RuntimeError('Headline diagnostics failed')
        audits = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^]]*)\]", output)
        audits += [(name, '') for name in re.findall(
            r"'([^'\n]+)' does not depend on any axioms", output)]
        if len(audits) != len(names) or {name for name, _ in audits} != set(names):
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
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        receipt = {
            'checked_at_utc': datetime.now(timezone.utc).isoformat(),
            'compiler': compiler,
            'source_sha256': after,
            'dependencies': {p['name']: p['rev'] for p in manifest['packages']},
            'headline_audits': records,
            'complete_types_and_axioms': output,
            'audit_source_sha256': digest(audit),
            'audit_log_sha256': digest(out / 'HeadlineAudit.log'),
            'scope': ('Generic same-base definable descent only; no numbered Section 4 lemma'
                      if selected else 'All public Section 4 theorems and function constructions currently imported by the section library; includes Lemmas 4.1–4.4 and 4.8, actual cell definitions and full label-base graph/paradigm definability, nondegenerate paradigm slopes, ordinary compatible-fibre slopes, balanced closed hulls/ball correspondence/internal symmetry, unary decomposition, parameterized cell definitions, and the independently checked singleton open-polydisc boundary'),
            'build_scope': 'Incremental selected Lake build; fresh complete-type and axiom consumer audit',
            'root_integration_checked': False,
        }
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        status.write_text('PASS\n')
        print(f'PASS: {len(names)} selected complete-type and permitted-axiom audits.')
        return 0
    except Exception as exc:
        status.write_text('FAIL\n')
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
