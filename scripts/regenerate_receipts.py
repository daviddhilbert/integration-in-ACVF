#!/usr/bin/env python3
"""Regenerate the committed verification receipts from a fresh local run.

Run after a passing project verification of the commit being described:

    lake build 2>&1 | tee .scratch/receipt-root-build.log
    lake env python3 scripts/verify_ci.py --use-lake-build
    python3 scripts/verify_promoted_foundations.py
    python3 scripts/regenerate_receipts.py --root-build-log .scratch/receipt-root-build.log

It rewrites the Section 2-5 VERIFICATION.json receipts from the verifiers'
fresh .scratch receipts (Section 5 through section 5/retain_verification.py),
refreshes verification/shared-foundation.json and writes a dated
verification/project-integrity-<date>.json. Hand-written notes of a replaced
receipt are kept under "superseded_receipt_notes" rather than deleted. The
proof inputs (Lean sources, pins, verifiers) must be committed and unchanged
since the verification run; CI for the commit is reported separately.
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
SCRATCH = ROOT / '.scratch'
ALLOWED = ['Classical.choice', 'Quot.sound', 'propext']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def require_unchanged(receipt_sources, label):
    for name, digest in receipt_sources.items():
        if sha(ROOT / name) != digest:
            raise RuntimeError(f'{label}: {name} changed since verification')


def section_receipt(number, stamp):
    checked = SCRATCH / f'section{number}-verified'
    if (checked / 'status.txt').read_text().strip() != 'PASS':
        raise RuntimeError(f'Section {number} has no passing fresh receipt')
    receipt = load(checked / 'receipt.json')
    require_unchanged(receipt['source_sha256'], f'Section {number}')
    target = ROOT / f'section {number}' / 'VERIFICATION.json'
    old = load(target)
    notes = {k: v for k, v in old.items() if k not in receipt and k != 'superseded_receipt_notes'
             and k not in ('regenerated', 'complete_type_sha256', 'full_receipt')}
    if notes:
        receipt['superseded_receipt_notes'] = {
            'note': 'Hand-written fields of the receipt checked at '
                    + str(old.get('checked_at_utc')) + '; historical, not re-verified.',
            **notes}
    receipt['regenerated'] = stamp
    return target, receipt, old


def axiom_scan(files):
    matches = []
    for path in files:
        text = path.read_text(encoding='utf-8')
        text = re.sub(r'/-.*?-/', '', text, flags=re.S)
        text = re.sub(r'--[^\n]*', '', text)
        text = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
        for line_number, line in enumerate(text.splitlines(), 1):
            if re.search(r'\b(?:sorry|admit|native_decide)\b', line) or re.match(
                    r'\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?axiom\b', line):
                matches.append(f'{path.relative_to(ROOT)}:{line_number}')
    return matches


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root-build-log', required=True)
    args = parser.parse_args()
    summary = load(SCRATCH / 'ci-verified' / 'summary.json')
    if set(summary.values()) != {'success'}:
        raise RuntimeError('Project verification did not pass: ' + json.dumps(summary))
    build_log = Path(args.root_build_log).read_text(encoding='utf-8', errors='replace')
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', build_log)
    if not jobs:
        raise RuntimeError('Root build log does not record a successful build')
    if git('status', '--porcelain', '--untracked-files=no', '--', '*.lean', 'lakefile.toml',
           'lake-manifest.json', 'lean-toolchain', 'scripts', 'section 2/verify.py',
           'section 3/verify.py', 'section 4/verify.py', 'section 5/verify.py',
           'section 6/verify.py', 'section 7/verify.py', 'verification/headline-types'):
        raise RuntimeError('Commit the proof inputs before writing receipts')
    commit = git('rev-parse', 'HEAD')
    today = datetime.now(timezone.utc).date().isoformat()
    stamp = {'date_utc': today, 'source_commit': commit,
             'by': 'scripts/regenerate_receipts.py',
             'note': 'Fresh local verifier receipt for this commit. CI for it is reported separately.'}
    manifest = load(ROOT / 'lake-manifest.json')
    pins = {p['name']: p['rev'] for p in manifest['packages']}

    exports = {}
    for number in (2, 3, 4):
        target, receipt, _ = section_receipt(number, stamp)
        dump(target, receipt)
        exports[number] = len(receipt['headline_audits'])
    subprocess.run([sys.executable, str(ROOT / 'section 5' / 'retain_verification.py')], cwd=ROOT, check=True)
    target = ROOT / 'section 5' / 'VERIFICATION.json'
    index = load(target)
    exports[5] = len(index['headline_audits'])
    section6 = load(SCRATCH / 'section6-verified' / 'certificate.json')
    section7 = load(SCRATCH / 'section7-verified' / 'receipt.json')
    exports[6] = len(section6['headlines'])
    exports[7] = section7['exports']
    return commit, today, stamp, pins, exports, jobs[-1], summary, index


def finish():
    commit, today, stamp, pins, exports, jobs, summary, index5 = main()
    previous5 = git('show', 'HEAD:section 5/VERIFICATION.json')
    previous5 = json.loads(previous5)
    if 'upstream_provenance' in previous5 and 'upstream_provenance' not in index5:
        index5['superseded_receipt_notes'] = {
            'note': 'Hand-written fields of the receipt checked at '
                    + str(previous5.get('checked_at_utc')) + '; historical, not re-verified.',
            'upstream_provenance': previous5['upstream_provenance']}
    index5['regenerated'] = stamp
    dump(ROOT / 'section 5' / 'VERIFICATION.json', index5)

    shared = load(ROOT / 'SHARED-FOUNDATION.json')
    promoted = load(SCRATCH / 'promoted-foundations' / 'status.json')
    record_path = ROOT / 'verification' / 'shared-foundation.json'
    old = load(record_path)
    keep = {k: old[k] for k in ('pre_promotion_checkpoint',) if k in old}
    superseded = {k: v for k, v in old.items()
                  if k not in ('pre_promotion_checkpoint', 'superseded_checkpoints')}
    record = {
        'status': 'PASS',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_commit': commit,
        'root_build': f'lake build ({jobs} jobs; all default roots, including IntegrationGeneratedBase)',
        'audit_command': 'lake env python3 scripts/verify_ci.py --use-lake-build',
        'audit_groups': summary,
        'section7_registered_declarations': exports[7],
        'shared_modules': len(shared['modules']),
        'shared_provider': pins['«hilbert-mathlib»'],
        'special_provider': pins['special_transformations'],
        'qe_provider': pins['acvf_qe'],
        'preflight': f'{len(pins)} exact dependency pins, {len(shared["modules"])} exact shared '
                     'source/compatibility identities (scripts/check_shared_foundation.py)',
        'scope': old.get('scope'),
        **keep,
        'promoted_foundations': {
            'modules': promoted['modules'],
            'unchanged_public_types': promoted['unchanged_public_types'],
            'full_types_and_axioms_sha256': sha(SCRATCH / 'promoted-foundations' / 'types-and-axioms.txt'),
        },
        'superseded_checkpoints': old.get('superseded_checkpoints', []) + [superseded],
        'regenerated': stamp,
    }
    dump(record_path, record)

    sections = []
    lean_files = []
    for number in range(2, 8):
        files = sorted((ROOT / f'section {number}').rglob('*.lean'))
        lean_files += files
        sections.append({'section': number, 'lean_sources': len(files),
                         'audited_exports': exports[number]})
    scan = axiom_scan(lean_files + [ROOT / 'IntegrationInACVF.lean', ROOT / 'IntegrationGeneratedBase.lean'])
    blueprint = subprocess.run([sys.executable, str(ROOT / 'scripts' / 'check_blueprint.py')],
                               cwd=ROOT, capture_output=True, text=True)
    baselines = {p.stem: {'declarations': None, 'sha256': sha(p)}
                 for p in sorted((ROOT / 'verification' / 'headline-types').glob('*.txt'))}
    integrity = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'proof_commit': commit,
        'proof_tree': git('rev-parse', 'HEAD^{tree}'),
        'proof_ci': {
            'status': 'not run by this script; check the Lean verification workflow for proof_commit',
            'url': 'https://github.com/daviddhilbert/integration-in-ACVF/actions/workflows/lean.yml',
            'earlier_passing_runs_on_main': [
                {'run_id': 44165197619, 'commit': 'ab4c0e8', 'conclusion': 'success'},
                {'run_id': 44608226709, 'commit': '5a69a5e', 'conclusion': 'success'},
            ],
        },
        'dependency_pins': pins,
        'root_build': {'result': 'PASS', 'jobs': int(jobs)},
        'whole_project_verifier': {'result': 'PASS', 'command': 'lake env python3 scripts/verify_ci.py --use-lake-build',
                                   'components': list(summary)},
        'headline_type_baselines': baselines,
        'sections': sections,
        'total_audited_section_exports': sum(exports.values()),
        'section_lean_sources': len(lean_files),
        'admission_and_custom_axiom_scan': {
            'result': 'PASS' if not scan else 'FAIL', 'files': len(lean_files) + 2,
            'patterns': 'sorry, admit, native_decide, axiom declarations',
            'excluded_comments_and_strings': True, 'matches': scan},
        'allowed_axioms': ALLOWED,
        'blueprint_check': json.loads(blueprint.stdout.strip().splitlines()[-1]) if blueprint.returncode == 0
                           else {'status': 'FAIL', 'output': (blueprint.stdout + blueprint.stderr)[-2000:]},
        'scope': 'Accepted Sections 2-7 scopes; exact hypotheses and corrections are recorded in the blueprint, '
                 'section status files and PAPER-CORRECTIONS.md. This integrity check is not an '
                 'unrestricted-paper completion claim.',
        'regenerated': stamp,
        'previous_receipt': 'verification/project-integrity-2026-11-16.json (proof commit 862aa44)',
    }
    for p in baselines:
        text = (ROOT / 'verification' / 'headline-types' / f'{p}.txt').read_text(encoding='utf-8')
        baselines[p]['declarations'] = len(re.findall(r'(?m)^@?\S+? :', text))
    if scan:
        raise RuntimeError('Admission scan matched: ' + ', '.join(scan[:20]))
    dump(ROOT / 'verification' / f'project-integrity-{today}.json', integrity)
    print(json.dumps({'status': 'PASS', 'proof_commit': commit, 'exports': exports,
                      'integrity': f'verification/project-integrity-{today}.json'}))


if __name__ == '__main__':
    finish()
