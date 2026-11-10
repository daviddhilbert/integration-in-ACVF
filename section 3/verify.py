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
    'ImaginaryParameters.WithTuple.preimage_map',
    'ImaginaryParameters.OverBase.preimage_map',
    'ImaginaryParameters.OverBase.empty_iff_real',
    'ImaginaryParameters.OverBase.forall_block',
    'ImaginaryParameters.OverBase.forall_finite',
    'ImaginaryParameters.OverBase.named_singleton',
    'ImaginaryParameters.OverBase.adjoin_iff',
    'ImaginaryParameters.with_iff_over_adjoin',
    'ImaginaryParameters.atomicWith_iff_atomic_adjoin',
    'ImaginaryParameters.isAtomicTupleOver_empty_iff',
    'ImaginaryParameters.unary_tuple_atomic_iff',
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
    'ImaginaryBaseFamilies.Family.image_on',
    'ImaginaryBaseFamilies.Algebraic.map_on',
    'ImaginaryBaseFamilies.Relation.comp_on',
    'ImaginaryBaseFamilies.parametric_atomic_of_output',
]
HEADLINES += [
    'ImaginaryBaseFamilies.rangeFamily_definable',
    'ImaginaryBaseFamilies.atomicWith_of_subsingleton',
]
HEADLINES += [
    'PuncturedDecomposition.' + name for name in (
        'mem_holes', 'proper_subset_in_hole', 'region_eq_sdiff_holes',
        'holes_disjoint', 'regions_disjoint', 'region_agreement',
        'exists_region', 'finite_punctured_decomposition')
]
HEADLINES += [
    'ProfileAtomicity.sameProfile_definable', 'ProfileAtomicity.badPoints_definable',
    'ProfileAtomicity.constant_on_classes',
]
HEADLINES += [
    'InfiniteCosets.map_nat_difference', 'InfiniteCosets.infinite_cosets_in_open_ball',
]
HEADLINES += [
    'MinimalBallSupport.' + name for name in (
        'exists_minimal_support', 'essential', 'region_mem_iff_subset',
        'strata_points', 'essential_ne_univ', 'region_of_agreement',
        'minimal_subset_support', 'minimal_unique')
]
HEADLINES += [
    'SupportFormulas.' + name for name in (
        'imp_definable', 'iff_definable', 'supportCodes_definable',
        'mem_supportCodes_iff', 'exists_finite', 'supportFamily_definable',
        'supportFamily_eq_preimage')
]
HEADLINES += [
    'MinimalBallSupport.support_covers',
    'PuncturedDecomposition.finite_decomposition_of_support',
]
HEADLINES += [
    'RegionFormulas.' + name for name in (
        'strictSubsetCodes_definable', 'mem_strictSubsetCodes_iff',
        'regionFamily_definable', 'family_compl', 'constantRelation',
        'positiveFamily_definable', 'regionFamily_eq_region',
        'positiveFamily_eq_preimage', 'positive_regions_cover')
]
HEADLINES += [
    'HoleFormulas.' + name for name in (
        'holeCodes_definable', 'pairRows_mem_iff', 'mem_holeCodes_iff',
        'maximal_iff_mem_holes', 'holeCodes_eq_pullback')
]
HEADLINES += [
    'CodeEquality.equalityCodes_definable', 'CodeEquality.pairRows_mem_iff',
    'CodeEquality.imageCodes_definable', 'AtomicRegions.uniform_property',
]
HEADLINES += ['ImaginaryBaseFamilies.pair_domain']
HEADLINES += [
    'ValuationRadius.' + name for name in (
        'closed_radius_le_of_subset', 'closed_radius_lt_of_subset_open',
        'open_radius_le_of_subset_closed', 'open_ne_closed')
]
HEADLINES += ['CodeEquality.imageCodeRelation_definable']
HEADLINES += ['ClassCoverage.wholeClass_definable', 'ClassCoverage.complete_type_cover']
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
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.ParameterPresentation.' + name for name in (
        'decode_encodeBall', 'decode_surjective', 'gamma_membership',
        'body_injective', 'codeDomain_definable', 'membership_definable',
        'presentation_definable')
]
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.FullBaseAtomicity.lemma_3_2']
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.AdjoinBall.' + name for name in (
        'embedCode_compatible', 'embedCode_definable', 'restrict_family',
        'restrict_relation', 'lemma_3_2')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullBaseAtomicity.OverBase.' + name for name in (
        'of_real', 'congr', 'inter', 'compl', 'union', 'preimage_comp',
        'exists_block', 'forall_block', 'forall_finite')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullGammaSyntax.' + name for name in (
        'proper_definable', 'Definable.of_real', 'Scalar.of_real', 'Definable.true_',
        'Definable.congr', 'Definable.and', 'Definable.not', 'Definable.or',
        'Definable.imp', 'Definable.iff', 'Definable.forall_finite',
        'Definable.reindex', 'Definable.exists_block', 'Definable.forall_block',
        'lt_definable', 'eq_definable', 'mul_definable', 'scalar_definable_iff',
        'unary_at', 'one_definable')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullGammaPoint.' + name for name in (
        'real_specialization', 'tupleControls_definable', 'minimal_controller_definable',
        'exists_definable_minimal_controller', 'scalar_sdiff', 'finset_min_definable',
        'finset_element_definable', 'named_one', 'named_mul', 'named_inv',
        'named_square_root', 'named_samples', 'gamma_definable_point')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullBaseAtomicity.OverBase.' + name for name in (
        'mono', 'preimage_map', 'adjoin_iff')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.AdjoinGamma.' + name for name in (
        'embedCode_compatible', 'embedCode_definable', 'restrict_vector', 'fibre_definable')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullGammaAtomicity.' + name for name in (
        'cutParameters_definable', 'lemma_3_3_one', 'lemma_3_3_finset',
        'lemma_3_3', 'lemma_3_3_unary')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullBallCoset.' + name for name in (
        'cosetRelation_definable', 'cosetFamily_definable', 'atomic_coset', 'atomicWith_to_adjoin')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullGammaRadius.' + name for name in (
        'radiusTail_definable', 'rv_preimage', 'radius_subgroup',
        'lemma_3_4', 'lemma_3_4_singleton', 'lemma_3_4_whole_field')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.PuncturedGeometry.' + name for name in (
        'PuncturedBall.body_subset_parent', 'PuncturedBall.body_subset_vf',
        'definable_punctured_decomposition')
]
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.FullCosetExceptions.finite_bad_cosets']
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullProfileCosets.' + name for name in (
        'vfDefault_val', 'vfDefault_definable', 'total_graph_definable',
        'total_class_relation_definable', 'constant_on_cosets')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.AdjoinGamma.restrict_family',
    'IntegrationInACVF.Section3ACVF.AdjoinGamma.named_scalar',
    'IntegrationInACVF.Section3ACVF.FullGammaAtomicity.lemma_3_3_one_unary',
    'IntegrationInACVF.Section3ACVF.FullGammaRadius.gamma_subgroup',
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.GammaCosetGeometry.' + name for name in (
        'vf_representative', 'gammaBall_mem_valuation', 'valuation_nat_unit',
        'cosetBody_mem', 'infinite_gamma_cosets', 'gammaBall_coded',
        'intermediate_radius', 'same_coset_of_difference')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.lemma_3_9',
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.corollary_3_10',
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.graph_extendByEmpty',
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.lemma_3_9_on',
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.corollary_3_10_on',
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.atomic_not_contains_vf',
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.lemma_3_9_open',
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.corollary_3_10_open',
    'IntegrationInACVF.Section3ACVF.PaperBalls.samePrimitiveType_symm',
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.CanonicalBallSupport.' + name for name in (
        'encodedBall_nonempty', 'encodedBall_isValBall', 'valuation_nontrivial',
        'encoded_avoids_finite_proper_subballs', 'ballFamily_laminar',
        'ballFamily_avoids', 'minimal_support_encoded', 'exists_unique_minimal_support')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallCodeGeometry.' + name for name in (
        'closed_raw_isBall', 'open_raw_isBall', 'underlying_isBall', 'encodedBall_coded')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.CanonicalSupportFamily.support_family_definable',
    'IntegrationInACVF.Section3ACVF.CanonicalSupportFamily.exists_definable_canonical_support',
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.CanonicalRegions.' + name for name in (
        'regions_definable', 'positive_family_definable',
        'exists_definable_positive_decomposition')
]
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.CanonicalHoles.holes_definable']
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallKindGeometry.' + name for name in (
        'open_raw_gammaBall', 'closed_raw_gammaBall', 'open_raw_isOpenBall',
        'closed_raw_isClosedBall', 'gammaBall_open_code', 'gammaBall_closed_code')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallKindPredicates.' + name for name in (
        'gammaBall_mem_valuation_closed', 'paper_closed_code', 'chartCodes_definable',
        'open_image_eq', 'closed_image_eq', 'open_family_definable', 'closed_family_definable')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.AtomicCanonicalRegions.' + name for name in (
        'uniform_property', 'unpunctured_family_definable', 'uniform_unpunctured')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallRadiusGeometry.' + name for name in (
        'valuation_dense', 'gamma_radius_unique_same_kind', 'gamma_open_ne_closed',
        'gamma_open_not_closed', 'open_closed_only_vf')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallRadiusGeometry.' + name for name in (
        'gammaBall_ne_vf', 'gamma_closed_ne_singleton', 'gamma_radius_unique')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.ValuativeCentreGeometry.' + name for name in (
        'valuativeCentre_unique', 'valuativeCentre_exists')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.PaperBallInvariants.' + name for name in (
        'singleton_ne_vf', 'hasRadius_exists', 'hasRadius_unique')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.OrdinaryCentreFibres.' + name for name in (
        'fieldValueEq_definable', 'fieldValueEq_iff', 'mem_ordinaryCentreFibre_iff',
        'relation_definable', 'image_definable', 'image_finite',
        'parent_test_definable', 'value_definable')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.UniformValuativeCentre.' + name for name in (
        'uniform_centre', 'exists_common_centre')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.SameRadiusCoverage.' + name for name in (
        'corollary_3_7_gamma', 'corollary_3_7_open', 'corollary_3_7_closed')
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
    'ImaginaryParameters.Base.adjoin',
    'ImaginaryParameters.IsAtomicOver',
    'ImaginaryParameters.IsAtomicTupleOver',
    'ImaginaryBaseFamilies.Family',
    'ImaginaryBaseFamilies.Relation',
    'ImaginaryBaseFamilies.With',
    'ImaginaryBaseFamilies.Algebraic',
    'ImaginaryBaseFamilies.AtomicWith',
    'ImaginaryBaseFamilies.CompleteType',
]
DEFINITIONS += ['PuncturedDecomposition.region', 'PuncturedDecomposition.holes']
DEFINITIONS += ['ProfileAtomicity.graph', 'ProfileAtomicity.sameProfile', 'ProfileAtomicity.badPoints']
DEFINITIONS += [
    'MinimalBallSupport.' + name for name in (
        'Supports', 'IsSupport', 'IsMinimalSupport', 'AvoidsFiniteProperSubballs')
]
DEFINITIONS += ['SupportFormulas.row', 'SupportFormulas.SupportCodes', 'SupportFormulas.SupportFamily']
DEFINITIONS += [
    'RegionFormulas.StrictSubsetCodes', 'RegionFormulas.regionFamily',
    'RegionFormulas.positiveFamily',
]
DEFINITIONS += ['HoleFormulas.pairRows', 'HoleFormulas.HoleCodes']
DEFINITIONS += ['CodeEquality.EqualityCodes', 'CodeEquality.imageCodes']
DEFINITIONS += ['CodeEquality.imageCodeRelation']
DEFINITIONS += ['ClassCoverage.wholeClass']
ACVF_DEFINITIONS = [
    'IntegrationInACVF.Section3ACVF.BallPresentation.' + name
    for name in ('codeDomain', 'decode', 'presentation', 'valuationBalls')
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity.radiusBall',
    'IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity.gammaBall',
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.ParameterPresentation.' + name for name in (
        'Name', 'codeDomain', 'decode', 'presentation', 'body')
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.FullBaseAtomicity.' + name for name in (
        'Base', 'OverBase', 'Family', 'Relation', 'Algebraic', 'AtomicWith')
]
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.AdjoinBall.AtomicOver']
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.FullGammaSyntax.Definable',
    'IntegrationInACVF.Section3ACVF.FullGammaSyntax.Scalar',
    'IntegrationInACVF.Section3ACVF.FullGammaPoint.Named',
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.AdjoinGamma.' + name for name in (
        'embedCode', 'vectorPullback')
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.FullGammaAtomicity.' + name for name in (
        'AtomicTuple', 'cutParameters', 'withGammaFinset', 'withGammaTuple')
]
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.FullBallCoset.CompleteType']
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.PuncturedGeometry.PuncturedBall',
    'IntegrationInACVF.Section3ACVF.PuncturedGeometry.PuncturedBall.body',
]
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.FullProfileCosets.vfDefault']
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.graphOn',
    'IntegrationInACVF.Section3ACVF.OpenBallConstancy.extendByEmpty',
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.PaperBalls.' + name for name in (
        'IsOpenBall', 'IsClosedBall', 'Radius', 'HasRadius', 'HasValuativeCentre',
        'IsThinAnnulus', 'PrimitiveKind', 'HasPrimitiveKind', 'SamePrimitiveType')
]
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.CanonicalBallSupport.ballFamily']
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.BallKindPredicates.openCodes',
    'IntegrationInACVF.Section3ACVF.BallKindPredicates.closedCodes',
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.OrdinaryCentreFibres.fieldValueEq',
    'IntegrationInACVF.Section3ACVF.OrdinaryCentreFibres.ordinaryCentreFibre',
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
            + '\n#eval IO.println "BEGIN_COMPACT_TYPES"\n'
            + 'set_option pp.explicit false\n'
            + '\n'.join('#check @' + name for name in names)
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
            'scope': ('Definition 3.1, interpreted-base calculus and finite laminar punctured decomposition; '
                      + ('actual Lemmas 3.2-3.3 over genuine real/Gamma/ball bases, with an original-base '
                         'definable nontrivial Gamma value explicit for 3.3; Lemma 3.4 at original-base '
                         'definable Gamma radii, singletons and VF; actual finite disjoint punctured '
                         'decomposition; finite coset-profile exceptions, Lemma 3.9 and Corollary 3.10 with the sequel open-ball convention and domain graphs; ' if args.acvf else '')
                      + 'the primitive-type classification of Lemma 3.6 and later section geometry remain open'),
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
