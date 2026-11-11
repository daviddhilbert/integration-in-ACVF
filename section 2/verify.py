#!/usr/bin/env python3
"""Compile and inspect the sequel's new Section 2 declarations."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / '.scratch' / 'section2-verified'
HEADLINES = [
    'IntegrationInACVF.Section2.corollary_2_15_real_base',
    'IntegrationInACVF.Section2.corollary_2_15',
]
HEADLINES += ['IntegrationInACVF.Section2.ConcreteVolumeForms.value_ne_zero', 'IntegrationInACVF.Section2.ConcreteVolumeForms.liftedValue_eq', 'IntegrationInACVF.Section2.ConcreteVolumeForms.nonzero_jacobian_of_preserves', 'IntegrationInACVF.Section2.VolumeCharacteristic.charZero', 'IntegrationInACVF.Section2.LiftFibreAvoidance.exists_outside', 'IntegrationInACVF.Section2.FixedLabelLift.base_subset', 'IntegrationInACVF.Section2.FixedLabelLift.source_base_subset', 'IntegrationInACVF.Section2.FixedLabelLift.target_base_subset', 'IntegrationInACVF.Section2.FixedLabelLift.source_mem', 'IntegrationInACVF.Section2.FixedLabelLift.target_mem', 'IntegrationInACVF.Section2.FixedLabelLift.fibreMap_bijective', 'IntegrationInACVF.Section2.FixedLabelLift.jacobian', 'IntegrationInACVF.Section2.FixedLabelLift.small_base', 'IntegrationInACVF.Section2.LiftFibreGeometry.nonzero_representatives', 'IntegrationInACVF.Section2.LiftFibreGeometry.projection', 'IntegrationInACVF.Section2.FibreVolumeEquations.ratio', 'IntegrationInACVF.Section2.FibreVolumeEquations.gamma_equation_of_ratio', 'IntegrationInACVF.Section2.GenericVolumeDescent.generic_equation', 'IntegrationInACVF.Section2.GammaVolumeDescent.pointwise_equation', 'IntegrationInACVF.Section2.VolumeBadLabels.mem_labels', 'IntegrationInACVF.Section2.VolumeBadLabels.dimension_le', 'IntegrationInACVF.Section2.ConcreteVolumeMorphisms.zero_arity', 'IntegrationInACVF.Section2.VolumeLiftDescent.corollary_2_34_positive', 'IntegrationInACVF.Section2.VolumeLiftDescent.corollary_2_34_essential', 'IntegrationInACVF.Section2.VolumeLiftDescent.corollary_2_34_of_finite_extension_reference']
DEFINITIONS = ['IntegrationInACVF.Section2.gammaRVGraph', 'IntegrationInACVF.Section2.ConcreteVolumeForms.RVForm', 'IntegrationInACVF.Section2.ConcreteVolumeForms.value', 'IntegrationInACVF.Section2.ConcreteVolumeForms.gammaValue', 'IntegrationInACVF.Section2.ConcreteVolumeForms.lift', 'IntegrationInACVF.Section2.ConcreteVolumeForms.liftedValue', 'IntegrationInACVF.Section2.ConcreteVolumeForms.PreservesOff', 'IntegrationInACVF.Section2.FixedLabelLift.labelBase', 'IntegrationInACVF.Section2.FixedLabelLift.source', 'IntegrationInACVF.Section2.FixedLabelLift.target', 'IntegrationInACVF.Section2.FixedLabelLift.fibreMap', 'IntegrationInACVF.Section2.VolumeBadLabels.labels', 'IntegrationInACVF.Section2.ConcreteVolumeMorphisms.RVCompatible', 'IntegrationInACVF.Section2.ConcreteVolumeMorphisms.GammaCompatible', 'IntegrationInACVF.Section2.ConcreteVolumeMorphisms.IsVolumeIsomorphism', 'IntegrationInACVF.Section2.ConcreteVolumeMorphisms.essentialForm', 'SpecialTransformations.Section9.FiniteHenselianExtensionReference', 'SpecialTransformations.Section9.HenselizedGaussGraphInput']
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
        sources = sorted((ROOT / 'section 2' / 'IntegrationSection2').glob('*.lean'))
        inputs = sources + [ROOT / p for p in (
            'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'section 2/verify.py')]
        before = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
        run(['lake', 'build', 'IntegrationSection2'], 'SectionBuild.log')
        compiler = run(['lake', 'env', 'lean', '--version'], 'Compiler.log').strip()
        audit = OUT / 'HeadlineAudit.lean'
        audit.write_text('import IntegrationSection2.Library\n'
                         'set_option pp.explicit true\nset_option pp.maxSteps 10000000\nset_option pp.deepTerms true\n'
                         + '\n'.join('#print ' + name for name in DEFINITIONS) + '\n'
                         + '\n'.join('#check @' + name + '\n#print axioms ' + name
                                     for name in HEADLINES) + '\n#eval IO.println \"BEGIN_COMPACT_TYPES\"\nset_option pp.explicit false\n'
                         + '\n'.join('#check @' + name for name in HEADLINES) + '\n', encoding='utf-8')
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
            'audit_source_sha256': digest(audit),
            'audit_log_sha256': digest(OUT / 'HeadlineAudit.log'),
            'scope': 'Corollary2.15; concrete positive and essential2.34 descent with explicit predecessor henselian graph or finite-extension reference input; degree-zero convention',
            'build_scope': 'Incremental Lake Section 2 build and fresh type/axiom audit',
        }
        (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
        status.write_text('PASS\n', encoding='utf-8')
        print(f'PASS: {len(HEADLINES)} Section2 complete types and standard-axiom audits;2.34 reference input remains explicit.')
        return 0
    except Exception as exc:
        status.write_text('FAIL\n', encoding='utf-8')
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
