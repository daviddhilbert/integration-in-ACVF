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
    'HasFiniteBallSupport.mono',
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
    'ImaginaryFamilies.Presentation.mem_pullback',
    'ImaginaryFamilies.Presentation.mem_relationPullback',
    'ImaginaryFamilies.Presentation.isDefinable_of_membership',
    'ImaginaryFamilies.Presentation.DefinableRelation.inter',
    'ImaginaryFamilies.Presentation.DefinableRelation.compl',
    'ImaginaryFamilies.Presentation.DefinableRelation.domain',
    'ImaginaryFamilies.Presentation.DefinableFamily.inter',
    'ImaginaryFamilies.Presentation.DefinableRelation.restrict',
    'ImaginaryFamilies.Presentation.DefinableRelation.range',
    'ImaginaryFamilies.Presentation.DefinableFamily.image_on',
    'ImaginaryFamilies.Presentation.Algebraic.map_on',
    'ImaginaryFamilies.Presentation.DefinableRelation.comp_on',
    'ImaginaryFamilies.exceptional_definable',
    'ImaginaryFamilies.traces_definable',
    'ImaginaryFamilies.splits_traces',
    'ImaginaryFamilies.atomic_below_complete_type',
    'ImaginaryFamilies.finite_exceptional',
    'ImaginaryFamilies.parametric_atomic',
    'ImaginaryFamilies.parametric_atomic_of_output',
    'ImaginaryFamilies.rangeFamily_definable',
    'ImaginaryFamilies.atomicWith_of_subsingleton',
    'empty_relation_check',
    'complete_type_relation_projections',
    'ImaginaryParameters.tupleCodes_definable',
    'ImaginaryParameters.vector_specialize',
    'ImaginaryParameters.WithTuple.specialize',
    'ImaginaryParameters.OverBase.specialize',
    'ImaginaryParameters.WithTuple.mono',
    'ImaginaryParameters.OverBase.mono',
    'ImaginaryParameters.WithTuple.reindex',
    'ImaginaryParameters.WithTuple.inter',
    'ImaginaryParameters.WithTuple.compl',
    'ImaginaryParameters.OverBase.of_real',
    'ImaginaryParameters.OverBase.inter',
    'ImaginaryParameters.OverBase.compl',
    'ImaginaryParameters.finite_ball_support',
    'ImaginaryParameters.WithTuple.preimage_comp',
    'ImaginaryParameters.OverBase.preimage_comp',
    'ImaginaryParameters.WithTuple.exists_block',
    'ImaginaryParameters.OverBase.exists_block',
    'ImaginaryBaseFamilies.Relation.inter',
    'ImaginaryBaseFamilies.Relation.compl',
    'ImaginaryBaseFamilies.Relation.domain',
    'ImaginaryBaseFamilies.Family.inter',
    'ImaginaryBaseFamilies.Relation.restrict',
    'ImaginaryBaseFamilies.Relation.range',
    'ImaginaryBaseFamilies.exceptional_definable',
    'ImaginaryBaseFamilies.traces_definable',
    'ImaginaryBaseFamilies.finite_exceptional',
    'ImaginaryBaseFamilies.atomic_below_complete_type',
    'ImaginaryBaseFamilies.parametric_atomic',
]
ACVF_HEADLINES = [
    'IntegrationInACVF.Section3ACVF.' + name for name in (
        'encodedBall_isKBall', 'encodedBalls_laminar', 'support_of_isBoolComb',
        'normalized_cMinimalOn', 'real_parametric_ball_atomic')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallPresentation.' + name for name in (
        'decode_encodeClosed', 'decode_encodeOpen', 'decode_surjective',
        'underlying_decode', 'codeDomain_definable', 'membership_definable',
        'presentation_definable', 'valuationBalls_laminar',
        'normalized_cMinimalOn_valuationBalls', 'underlying_valuationBall',
        'lemma_3_2_real_base')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.GammaAtomicity.' + name for name in (
        'fibre_decode', 'cutting_parameters_definable',
        'fibre_definable_of_definable_parameters', 'definableWith_of_real',
        'lemma_3_3_real_base')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallCosetAtomicity.' + name for name in (
        'cosetRelation_definable', 'cosetRelation_fibre', 'cosetFamily_definable',
        'cosetFamily_disjoint', 'atomic_ball_coset_below_complete_type')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity.' + name for name in (
        'radiusTail_definable', 'radius_subgroup', 'lemma_3_4_named_radius')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity.' + name for name in (
        'radiusTail_definable_of_value', 'radiusBall_eq_gammaBall',
        'lemma_3_4_real_base', 'lemma_3_4_singleton', 'lemma_3_4_whole_field')
]
DEFINITIONS = [
    'GeneratesCompleteType', 'IsAtomic', 'Splits',
    'IsLaminar', 'HasFiniteBallSupport',
    'DefinableFamilies.IsAlgebraicPoint', 'CMinimalOn', 'cutIndices', 'cutUnion',
    'ImaginaryFamilies.Presentation',
    'ImaginaryFamilies.Presentation.IsDefinable',
    'ImaginaryFamilies.Presentation.DefinableWith',
    'ImaginaryFamilies.Presentation.Algebraic',
    'ImaginaryFamilies.Presentation.AtomicWith',
    'ImaginaryParameters.tuplePresentation',
    'ImaginaryParameters.vectorPullback',
    'ImaginaryParameters.WithTuple',
    'ImaginaryParameters.Base',
    'ImaginaryParameters.OverBase',
    'ImaginaryBaseFamilies.Family',
    'ImaginaryBaseFamilies.Relation',
    'ImaginaryBaseFamilies.With',
    'ImaginaryBaseFamilies.Algebraic',
    'ImaginaryBaseFamilies.AtomicWith',
    'ImaginaryBaseFamilies.CompleteType',
]
ACVF_DEFINITIONS = [
    'IntegrationInACVF.Section3ACVF.BallPresentation.' + name
    for name in ('codeDomain', 'decode', 'presentation', 'valuationBalls')
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
            ('import IntegrationSection3ACVF.Library\n' if args.acvf
             else 'import IntegrationSection3.Library\n')
            + 'set_option pp.explicit true\n'
            + '\n'.join('#print ' + PREFIX + name for name in DEFINITIONS)
            + ('\n' + '\n'.join('#print ' + name for name in ACVF_DEFINITIONS) if args.acvf else '')
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
            'scope': ('Definition 3.1 and generic real/imaginary-index parametric atomicity; '
                      + ('actual ACVF real-base cases of Lemmas 3.2 and 3.3, '
                         'and Lemma 3.4 for definable Gamma radii, singletons and VF; ' if args.acvf else '')
                      + 'full C-bullet bases with additional imaginary names remain open'),
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
