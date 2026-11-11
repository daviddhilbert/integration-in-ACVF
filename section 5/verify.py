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
    'IntegrationInACVF.Section5.replaceCoordinateMap',
    'IntegrationInACVF.Section5.activeFocusSection',
    'IntegrationInACVF.Section5.activeFocusSection_apply',
    'IntegrationInACVF.Section5.focusSectionFun',
    'IntegrationInACVF.Section5.focusSectionMap',
    'IntegrationInACVF.Section5.focusSectionMap_active',
    'IntegrationInACVF.Section5.focusSectionMap_inactive',
    'IntegrationInACVF.Section5.focusSectionMap_sameRV',
    'IntegrationInACVF.Section5.unary_focusSectionMap_eq',
    'IntegrationInACVF.Section5.common_gamma_presentation',
    'IntegrationInACVF.Section5.lemma_5_1',
    'IntegrationInACVF.Section5.gamma_identity_graph',
    'IntegrationInACVF.Section5.gamma_composition_graph',
    'IntegrationInACVF.Section5.lemma_5_1_gamma_presented',
    'IntegrationInACVF.Section5.lemma_5_1_real_base',
    'IntegrationInACVF.Section5.sameRV_map_definable',
    'IntegrationInACVF.Section5.pulledFocusLocus_definable',
    'IntegrationInACVF.Section5.unaryVFProjection',
    'IntegrationInACVF.Section5.pulledFocusCentre_graph',
    'IntegrationInACVF.Section5.pulledFocus',
    'IntegrationInACVF.Section5.focusSection_locus',
    'IntegrationInACVF.Section5.unary_focusSection_idempotent',
    'IntegrationInACVF.Section5.pulledFocusSection',
    'IntegrationInACVF.Section5.map_pulledFocusSection',
    'IntegrationInACVF.Section5.pulledFocusSection_constant',
    'IntegrationInACVF.Section5.pulledFocusSection_idempotent',
    'IntegrationInACVF.Section5.PullSelected',
    'IntegrationInACVF.Section5.pullSelected_sameRV',
    'IntegrationInACVF.Section5.pullSelected_section',
    'IntegrationInACVF.Section5.pulledFocusLocus',
    'IntegrationInACVF.Section5.pulledFocusLocus_pullback',
    'IntegrationInACVF.Section5.pulledFocusLocus_subset',
    'IntegrationInACVF.Section5.pulledFocusCentre',
    'IntegrationInACVF.Section5.pulledFocusCentre_apply',
    'IntegrationInACVF.Section5.unary_sameRV_of_tagged_labels',
    'IntegrationInACVF.Section5.pulledFocusCentre_independent',
    'IntegrationInACVF.Section5.pulledFocusCentre_mem',
    'IntegrationInACVF.Section5.pulledFocusGeometry',
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
    'IntegrationInACVF.Section5.sameRV_zero_iff',
    'IntegrationInACVF.Section5.eq_of_sameRV_of_zero',
    'IntegrationInACVF.Section5.unary_open_polydisc_sameRV',
    'IntegrationInACVF.Section5.rvCellImage',
    'IntegrationInACVF.Section5.contractible_of_centred_open_images',
    'IntegrationInACVF.Section5.UnaryChain',
    'IntegrationInACVF.Section5.UnaryChain.toMap',
    'IntegrationInACVF.Section5.UnaryChain.bijective',
    'IntegrationInACVF.Section5.UnaryChain.append',
    'IntegrationInACVF.Section5.UnaryChain.append_toMap',
    'IntegrationInACVF.Section5.primitiveUnaryCoordinate',
    'IntegrationInACVF.Section5.primitive_unaryRelative',
    'IntegrationInACVF.Section5.specialUnaryChain',
    'IntegrationInACVF.Section5.specialUnaryChain_toMap',
    'IntegrationInACVF.Section5.special_bijection_unary_factorization',
    'IntegrationInACVF.Section5.unary_bijection_factorization',
    'IntegrationInACVF.Section5.unaryShift',
    'IntegrationInACVF.Section5.unaryShift_injective',
    'IntegrationInACVF.Section5.unaryShift_add_cancel',
    'IntegrationInACVF.Section5.unaryShift_open_polydisc',
    'IntegrationInACVF.Section5.unaryShift_eq_zero_iff',
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
            'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
            'IntegrationInACVF.lean', 'section 5/verify.py')]
        before = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        run(['python3', 'scripts/prepare_ci.py'], 'DependencyPins.log')
        run(['lake', 'build', 'IntegrationSection5'], 'SectionBuild.log')
        compiler = run(['lake', 'env', 'lean', '--version'], 'Compiler.log').strip()
        audit = OUT / 'HeadlineAudit.lean'
        audit.write_text('import IntegrationSection5.Library\n'
                         'import IntegrationSection5.GeometryLibrary\n'
                         'set_option pp.explicit true\n'
                         'set_option pp.universes true\n'
                         'set_option pp.fullNames true\n'
                         'set_option pp.funBinderTypes true\n'
                         'set_option pp.proofs true\n'
                         'set_option pp.deepTerms true\n'
                         'set_option pp.maxSteps 1000000\n'
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
        types = {}
        for name, block in audits:
            axioms = {re.sub(r'\.\{[^}]*\}$', '', a.strip())
                      for a in block.split(',') if a.strip()}
            if axioms - ALLOWED:
                raise RuntimeError('Unexpected axioms for ' + name)
            records.append({'name': name, 'axioms': sorted(axioms)})
            match = re.search(r'(?m)^@' + re.escape(name) + r'(?:\.\{[^}]*\})?\s*:', output)
            if match is None:
                raise RuntimeError('Missing complete type for ' + name)
            end = output.index("\n'" + name + "'", match.start())
            types[name] = output[match.start():end]
            if '⋯' in types[name]:
                raise RuntimeError('Pretty-printer omitted part of type for ' + name)
        if sources != sorted((ROOT / 'section 5' / 'IntegrationSection5').glob('*.lean')):
            raise RuntimeError('Section source inventory changed during verification')
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
            'complete_types': types,
            'audit_source_sha256': digest(audit),
            'audit_log_sha256': digest(OUT / 'HeadlineAudit.log'),
            'scope': 'Lemma 5.1 over real and original Gamma bases; quotient and relatively unary calculus. See STATUS.md for the exact scope; not a proof of Lemma 5.2.',
            'build_scope': 'Incremental Lake Section 5 build and fresh full-type/axiom audit',
        }
        (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
        status.write_text('PASS\n', encoding='utf-8')
        print(f'PASS: Section 5 proof batch; {len(HEADLINES)} complete type/axiom audits.')
        return 0
    except Exception as exc:
        status.write_text('FAIL\n', encoding='utf-8')
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
