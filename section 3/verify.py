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
HEADLINES += ['ImaginaryBaseFamilies.pair_domain', 'RegionFormulas.single_positive_region']
HEADLINES += [
    'ValuationRadius.' + name for name in (
        'closed_radius_le_of_subset', 'closed_radius_lt_of_subset_open',
        'open_radius_le_of_subset_closed', 'open_ne_closed')
]
HEADLINES += ['CodeEquality.imageCodeRelation_definable']
HEADLINES += ['ClassCoverage.wholeClass_definable', 'ClassCoverage.complete_type_cover']
HEADLINES += [
    'ValuationEnlargement.strict_enlargement',
    'ValuationEnlargement.closed_ssubset_closed', 'ValuationEnlargement.closed_ssubset_open',
    'AffineHoleCosets.congr', 'AffineHoleCosets.cosets_injective',
    'AffineHoleCosets.affine_mem_closed', 'AffineHoleCosets.exists_new_coset',
    'BallInclusionFormulas.subsetCodes_definable',
    'BallInclusionFormulas.mem_subsetCodes_iff', 'BallInclusionFormulas.enlargement_definable',
    'DefinablePartitions.cell_subordinate', 'DefinablePartitions.cells_disjoint',
    'DefinablePartitions.cell_definable', 'DefinablePartitions.exists_partition',
    'CoarsePartition.region_not_small', 'CoarsePartition.common_support',
    'CoarsePartition.outer_piece_cover', 'CoarsePartition.unique_outer_piece_at_bound',
    'BoundedCoverFormulas.coverWitness_definable', 'BoundedCoverFormulas.tupleCover_definable',
    'BoundedCoverFormulas.atMostCover_definable', 'BoundedCoverFormulas.atMostCover_iff',
    'BoundedCoverFormulas.uncoveredFamily_definable',
    'AtomicPuncturedPartition.subsingleton',
    'ImaginaryBaseFamilies.Relation.finite_ball_support',
    'ImaginaryBaseImages.image_definable', 'ImaginaryBaseImages.preimage_definable',
    'ImaginaryBaseImages.completeType_image', 'ImaginaryBaseImages.family_preimage_definable',
    'DefinableHoleRefinement.names_finite', 'DefinableHoleRefinement.enlarged_proper',
    'DefinableHoleRefinement.body_nonempty', 'DefinableHoleRefinement.body_subset_region',
    'DefinableHoleRefinement.body_strict', 'DefinableHoleRefinement.body_strict_of_hole_enlargement',
    'DefinableHoleRefinement.body_definable', 'DefinableHoleRefinement.body_eq_region',
    'ImaginaryTupleFormulas.inter', 'ImaginaryTupleFormulas.neg',
    'ImaginaryTupleFormulas.reindex', 'ImaginaryTupleFormulas.exists_finite',
    'ImaginaryTupleFormulas.exists_block', 'ImaginaryTupleFormulas.coordinate_eq',
    'ImaginaryTupleFormulas.coordinate_mem', 'ImaginaryTupleFormulas.strict_subset',
    'ImaginaryTupleFormulas.exists_points', 'AffineHoleFormulas.expansion_definable',
    'AffineHoleClosure.mk_step', 'AffineHoleClosure.subset_closure',
    'AffineHoleClosure.step_mem_closure', 'AffineHoleClosure.closure_strict',
    'AffineHoleClosure.affine_mem_closed_parent', 'AffineHoleClosure.closure_stays_in_parent',
    'PuncturedSupport.supports', 'PuncturedSupport.region_parent',
    'PuncturedSupport.minimal_eq', 'PuncturedSupport.positive_names_singleton',
    'AtomicRegions.refinement_eq',
    'PunctureCuts.exists_avoiding', 'PunctureCuts.not_subset_old_holes',
    'PunctureCuts.strict_replacement',
    'PunctureFormulas.puncturedFamily_definable', 'PunctureFormulas.transported_definable',
    'PunctureFormulas.add_transport_definable',
]
HEADLINES += ['FiniteBallHulls.finite_strict_bound', 'FiniteBallHulls.open_ssubset_open', 'FiniteBallHulls.finite_points_in_proper_open', 'FiniteBallHulls.finite_closed_balls_in_proper_open', 'FibreSupportFormulas.supportsTuple_definable', 'FibreSupportFormulas.supportsTuple_iff', 'FibreSupportFormulas.hasSupport_definable', 'FibreSupportFormulas.hasSupport_family', 'FibreSupportFormulas.hasSupport_of_support', 'FibreSupportFormulas.card_le_of_hasSupport', 'FibreSupportFormulas.uniform_minimal_card', 'FibreSupportFormulas.supportMember_definable', 'FibreSupportFormulas.supportMember_eq_family', 'FibreSupportFormulas.supportMember_iff_canonical', 'RelationalPreimages.family_definable', 'CoarseRelationFibres.infinite_preimage', 'CoarseRelationFibres.finite_intersection', 'CoarseRelationFibres.finite_family_bound', 'CoarseRelationFibres.coarse_indices_finite']

HEADLINES += ['SupportInsideBall.trimmed_support', 'SupportInsideBall.support_subset_parent', 'SupportInsideBall.parent_region_subset', 'SupportInsideBall.parent_mem_small_complement', 'SupportInsideBall.proper_support_of_not_small', 'FiniteCofiniteClasses.outside_finite_same_profile', 'FiniteCofiniteClasses.finite_or_cofinite', 'QuotientCover.image_finite_of_finite_cover', 'QuotientCover.meets_infinite', 'QuotientCover.complement_infinite', 'FiniteClosedHull.radius_unique', 'FiniteClosedHull.open_hull_subset', 'FiniteClosedHull.exists_hull', 'AtomicFiniteFibres.hasMore_definable', 'AtomicFiniteFibres.exists_injective_of_card_le', 'AtomicFiniteFibres.not_hasMore_iff', 'AtomicFiniteFibres.uniform_bound', 'NamedFamilyFibres.equal_family', 'NamedFamilyFibres.singleton_of_definable', 'NamedFamilyFibres.unary_family', 'NamedFamilyFibres.binary_fibre', 'ProperInverseSupports.proper_inverse_supports']

HEADLINES += ['FiniteClosedHull.radius_lt_of_open_cover', 'CoverRadiusFormulas.covers_definable', 'CoverRadiusFormulas.greatest_definable']

HEADLINES += ['FiniteClosedHull.exists_of_finite_hulls', 'FiniteClosedHull.radius_ne_zero_of_infinite']

HEADLINES += ['RelationProjections.domain_definable', 'RelationProjections.range_definable', 'RelationProjections.surjective', 'RelativeQuotientCut.closed_saturated', 'RelativeQuotientCut.exists_cut', 'UniformHullSeparation.impossible']

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
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.OrdinaryRadiusFibres.' + name for name in (
        'radiusCodes_definable', 'code_has_radius', 'hasRadius_code',
        'image_eq', 'relation_definable', 'mem_ordinaryRadiusFibre_iff',
        'image_definable', 'image_finite', 'parent_test_definable', 'value_definable')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.UniformRadius.' + name for name in (
        'radius_bottom_iff', 'radius_infinity_iff', 'nonordinary_cases',
        'uniform_radius', 'exists_common_radius')
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.valuation_le_of_gamma_le',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.valuation_lt_of_gamma_lt',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.ordinary_presentation',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.gammaBall_centre_mem',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.gammaBall_isBall',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.closed_ball_coded',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.vf_ssubset_lift',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.vf_eq_lift',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.gamma_same_kind_eq_of_subset',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.closed_not_subset_open_same_radius',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.proper_same_radius_kinds',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.gamma_radius_le_of_subset',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.open_inside_closed_same_radius',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.gammaBall_strict_enlargement',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.closed_inside_parent',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.gammaBall_proper_in_vf',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.singleton_strict_enlargement',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.closed_fixed_radius_unique',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.closed_ordinary_presentation',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.closed_supersets_unique',
    'IntegrationInACVF.Section3ACVF.BallEnlargementGeometry.fixed_radius_enlargements_finite',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.radiusClass_definable',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.expansion_definable',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.additional_names_finite',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.no_named_closed_intermediate',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.support_radius_named',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.no_ordinary_hole_gap',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.no_singleton_hole_in_ordinary_parent',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.no_hole_in_vf_parent',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.no_vf_positive_parent',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.no_hole_in_singleton_parent',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.hole_maximal_open',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.punctured_parent_shape',
    'IntegrationInACVF.Section3ACVF.AffineArithmetic.graph_definable',
    'IntegrationInACVF.Section3ACVF.AffineArithmetic.mem_graph_iff',
    'IntegrationInACVF.Section3ACVF.AffineArithmetic.graph_overBase',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.open_ordinary_presentation',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.coset_presentation',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.class_eq_of_mem',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.same_name_of_class',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.affine_output_unique',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.radiusClass_definable',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.expansion_definable',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.additional_names_finite',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.exists_additional_hole',
    'IntegrationInACVF.Section3ACVF.AffineHoleCut.holes_subsingleton',
    'IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.piece_body',
    'IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.punctured_piece_thin',
    'IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.unpunctured_piece_kind',
    'IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.common_kind',
    'IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.same_primitive_type',
    'IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.lemma_3_6',
    'IntegrationInACVF.Section3ACVF.PuncturedImageComponents.partition_subsingleton',
    'IntegrationInACVF.Section3ACVF.PuncturedImageComponents.image_one_positive_region',
    'IntegrationInACVF.Section3ACVF.PuncturedImageComponents.image_of_single_canonical_component',
    'IntegrationInACVF.Section3ACVF.PuncturedImageComponents.image_of_atomic_punctured',
    'IntegrationInACVF.Section3ACVF.PuncturedImageComponents.image_is_punctured',
    'IntegrationInACVF.Section3ACVF.PrimitiveImages.atomic_image',
    'IntegrationInACVF.Section3ACVF.PrimitiveImages.lemma_3_8',
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.FullRelationSupports.preimages_definable',
    'IntegrationInACVF.Section3ACVF.FullRelationSupports.support_graph_definable',
    'IntegrationInACVF.Section3ACVF.FullRelationSupports.uniform_support_card',
    'IntegrationInACVF.Section3ACVF.FullRelationSupports.exists_proper_inverse_supports',
    'IntegrationInACVF.Section3ACVF.FullGammaFamilyConstancy.graph_of_fibres',
    'IntegrationInACVF.Section3ACVF.FullGammaFamilyConstancy.constant',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.covers_definable',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.span_definable',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.mem_covers_iff',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.cover_from_hull',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.cover_value_le_hull',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.mem_span_iff_value',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.span_eq_gammaFibre',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.equal_of_inter',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.proper_ball_in_maximal',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.class_subset_body',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.covers_body',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.classes_disjoint',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.class_proper_parent',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.classes_infinite',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.test_ball',
    'IntegrationInACVF.Section3ACVF.MaximalSubballFamilies.contained_family_definable',
    'IntegrationInACVF.Section3ACVF.MaximalSubballFamilies.classes_definable',
    'IntegrationInACVF.Section3ACVF.MaximalSubballFamilies.finite_or_cofinite',
    'IntegrationInACVF.Section3ACVF.InfiniteOrdinaryBalls.open_infinite',
    'IntegrationInACVF.Section3ACVF.InfiniteOrdinaryBalls.closed_infinite',
    'IntegrationInACVF.Section3ACVF.NativeBallHulls.closed_hull_for_ball',
    'IntegrationInACVF.Section3ACVF.NativeBallHulls.finite_support_hull',
    'IntegrationInACVF.Section3ACVF.UniformSupportHull.preimage_subset_supportLift',
    'IntegrationInACVF.Section3ACVF.UniformSupportHull.preimage_infinite',
    'IntegrationInACVF.Section3ACVF.UniformSupportHull.supportLift_infinite',
    'IntegrationInACVF.Section3ACVF.UniformSupportHull.common_hull_radius',
    'IntegrationInACVF.Section3ACVF.ClosedTraceFamilies.named_ball_body',
    'IntegrationInACVF.Section3ACVF.ClosedTraceFamilies.meets_named_ball',
    'IntegrationInACVF.Section3ACVF.ClosedTraceFamilies.finite_or_cofinite_native_cut',
    'IntegrationInACVF.Section3ACVF.OrdinarySeparation.not_finite_rows',
    'IntegrationInACVF.Section3ACVF.OrdinarySeparation.not_finite_rows_unnamed_radius',
    'IntegrationInACVF.Section3ACVF.Separation.unpunctured_body',
    'IntegrationInACVF.Section3ACVF.Separation.for_punctured_target',
    'IntegrationInACVF.Section3ACVF.Separation.lemma_3_11',
    'IntegrationInACVF.Section3ACVF.SeparationFunctions.open_nonempty',
    'IntegrationInACVF.Section3ACVF.SeparationFunctions.closed_nonempty',
    'IntegrationInACVF.Section3ACVF.SeparationFunctions.punctured_nonempty',
    'IntegrationInACVF.Section3ACVF.SeparationFunctions.open_infinite',
    'IntegrationInACVF.Section3ACVF.SeparationFunctions.no_function_from_open',
    'IntegrationInACVF.Section3ACVF.SeparationFunctions.no_finite_to_one_to_open',
    'IntegrationInACVF.Section3ACVF.OpenImages.open_one_component',
    'IntegrationInACVF.Section3ACVF.OpenImages.body_eq_parent',
    'IntegrationInACVF.Section3ACVF.OpenImages.lemma_3_13',
]
HEADLINES += [
    'PolynomialSpecialization.finite_zero_specializations',
    'FibreEqualityFormulas.equalFibres_definable',
    'FibreEqualityFormulas.compose_definable',
    'BivariateCoordinates.ne_zero_iff',
    'BivariateCoordinates.eval_coordinates',
    'BivariateCoordinates.eval₂_coordinates',
]
ACVF_HEADLINES += [
    'IntegrationInACVF.Section3ACVF.PolynomialEscape.outside_closed',
    'IntegrationInACVF.Section3ACVF.PolynomialEscape.finite_polynomial_escape',
    'IntegrationInACVF.Section3ACVF.PolynomialEscape.same_rv_escape',
    'IntegrationInACVF.Section3ACVF.PolynomialEscape.closed_escape_in_rv_fibre',
    'IntegrationInACVF.Section3ACVF.AtomicPolynomialRoots.rootSet_definable',
    'IntegrationInACVF.Section3ACVF.AtomicPolynomialRoots.nonzero_on_complete_type',
    'IntegrationInACVF.Section3ACVF.AtomicPolynomialRoots.specialization_nonzero_on_complete_type',
    'IntegrationInACVF.Section3ACVF.AtomicPolynomialRoots.specialization_parameterField',
    'IntegrationInACVF.Section3ACVF.BallCentreElimination.centres_definable',
    'IntegrationInACVF.Section3ACVF.BallCentreElimination.graph_definable',
    'IntegrationInACVF.Section3ACVF.BallCentreElimination.on_coset',
    'IntegrationInACVF.Section3ACVF.BallCentreElimination.adjoin_elimination',
    'IntegrationInACVF.Section3ACVF.MultivariatePolynomialSupport.rv_term_eq_of_support',
    'IntegrationInACVF.Section3ACVF.MultivariatePolynomialSupport.formula_iff_of_support',
    'IntegrationInACVF.Section3ACVF.GammaSpecialization.specialize',
    'IntegrationInACVF.Section3ACVF.GammaSpecialization.parameterField_unchanged',
    'IntegrationInACVF.Section3ACVF.GammaSpecialization.specialize_preserving_field',
    'IntegrationInACVF.Section3ACVF.GammaPairFormula.presentation',
    'IntegrationInACVF.Section3ACVF.PolynomialSeparation.open_subset_vf',
    'IntegrationInACVF.Section3ACVF.PolynomialSeparation.zeroSet_mem_iff',
    'IntegrationInACVF.Section3ACVF.PolynomialSeparation.nonzero_on_product',
    'IntegrationInACVF.Section3ACVF.ClosedImageObstruction.with_definable_subgroup',
    'IntegrationInACVF.Section3ACVF.ClosedImageObstruction.not_closed',
    'IntegrationInACVF.Section3ACVF.ClosedImageObstruction.lemma_3_14',
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
DEFINITIONS += ['ClassCoverage.wholeClass', 'PunctureFormulas.puncturedFamily',
                'PunctureFormulas.transported', 'AffineHoleCosets.affine',
                'BallInclusionFormulas.SubsetCodes', 'DefinablePartitions.cell',
                'CoarsePartition.SmallIn', 'CoarsePartition.CoveredBy',
                'BoundedCoverFormulas.CoverWitness', 'BoundedCoverFormulas.TupleCover',
                'BoundedCoverFormulas.AtMostCover', 'ImaginaryBaseImages.graphOn', 'DefinableHoleRefinement.original',
                'DefinableHoleRefinement.enlarged', 'DefinableHoleRefinement.body',
                'AffineHoleClosure.step', 'AffineHoleClosure.closure',
                'ImaginaryTupleFormulas.Predicate', 'AffineHoleFormulas.expansion']
DEFINITIONS += ['FibreSupportFormulas.SupportsTuple', 'FibreSupportFormulas.HasSupport', 'FibreSupportFormulas.SupportMember', 'RelationalPreimages.family']

DEFINITIONS += ['SupportInsideBall.trimmed', 'QuotientCover.meets', 'FiniteClosedHull.IsHull', 'AtomicFiniteFibres.HasMore']

DEFINITIONS += ['CoverRadiusFormulas.covers', 'CoverRadiusFormulas.greatest']

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
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.OrdinaryRadiusFibres.ordinaryRadiusFibre',
    'IntegrationInACVF.Section3ACVF.OrdinaryRadiusFibres.RadiusCodes',
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.radiusClass',
    'IntegrationInACVF.Section3ACVF.NamedClosedHoleCut.expansion',
    'IntegrationInACVF.Section3ACVF.AffineArithmetic.expression',
    'IntegrationInACVF.Section3ACVF.AffineArithmetic.term',
    'IntegrationInACVF.Section3ACVF.AffineArithmetic.graph',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.radiusClass',
    'IntegrationInACVF.Section3ACVF.AffineHoleGeometry.expansion',
    'IntegrationInACVF.Section3ACVF.PrimitiveDecomposition.piece',
    'IntegrationInACVF.Section3ACVF.PrimitiveImages.OnePrimitiveComponent',
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.FullRelationSupports.preimages',
    'IntegrationInACVF.Section3ACVF.FullGammaFamilyConstancy.Graph',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.covers',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.order',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.span',
    'IntegrationInACVF.Section3ACVF.SupportHullRadius.supportLift',
    'IntegrationInACVF.Section3ACVF.MaximalSubballGeometry.classes',
    'IntegrationInACVF.Section3ACVF.Separation.unpunctured',
]
DEFINITIONS += [
    'PolynomialSpecialization.specialize',
    'FibreEqualityFormulas.equalFibres',
    'BivariateCoordinates.equiv',
]
ACVF_DEFINITIONS += [
    'IntegrationInACVF.Section3ACVF.BallCentreElimination.centres',
    'IntegrationInACVF.Section3ACVF.BallCentreElimination.graph',
    'IntegrationInACVF.Section3ACVF.MultivariatePolynomialSupport.term',
    'IntegrationInACVF.Section3ACVF.MultivariatePolynomialSupport.formula',
]

HEADLINES += ['PairMapFibres.graph_definable', 'PartialInverse.graph_eq', 'PartialInverse.graph_definable', 'ValuationProgressions.error_lt', 'ValuationProgressions.affine_mem_open']
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.OpenSubballImages.image_open_of_atomic', 'IntegrationInACVF.Section3ACVF.OpenBallRVGeometry.rv_sub_constant', 'IntegrationInACVF.Section3ACVF.RVFibreSubballs.exists_subball', 'IntegrationInACVF.Section3ACVF.RVDifferencePairs.difference_vf', 'IntegrationInACVF.Section3ACVF.RVDifferencePairs.difference_graph_definable', 'IntegrationInACVF.Section3ACVF.RVDifferencePairs.pair_graph_definable', 'IntegrationInACVF.Section3ACVF.RVPairPreservation.rv_difference', 'IntegrationInACVF.Section3ACVF.RVPairConstancy.graph_eq', 'IntegrationInACVF.Section3ACVF.RVPairConstancy.family_rv', 'IntegrationInACVF.Section3ACVF.RVPairConstancy.constant', 'IntegrationInACVF.Section3ACVF.RVMapRelation.difference_sorted', 'IntegrationInACVF.Section3ACVF.RVMapRelation.same_basepoint', 'IntegrationInACVF.Section3ACVF.RVMapRelation.right_unique', 'IntegrationInACVF.Section3ACVF.RVInverse.inverse_on', 'IntegrationInACVF.Section3ACVF.RVInverse.inverse_right', 'IntegrationInACVF.Section3ACVF.RVInverse.inverse_injOn', 'IntegrationInACVF.Section3ACVF.RVInverse.inverse_graph_definable', 'IntegrationInACVF.Section3ACVF.RVInverse.atomic_open_image', 'IntegrationInACVF.Section3ACVF.RVMapBijection.left_unique', 'IntegrationInACVF.Section3ACVF.RVMapBijection.difference_iff', 'IntegrationInACVF.Section3ACVF.RVIntegerSequences.sequence_rv', 'IntegrationInACVF.Section3ACVF.RVIntegerEquivariance.affine_mem', 'IntegrationInACVF.Section3ACVF.RVIntegerEquivariance.integer_equivariance']
DEFINITIONS += ['PairMapFibres.family', 'PairMapFibres.graph']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.RVDifferencePairs.difference', 'IntegrationInACVF.Section3ACVF.RVPairConstancy.family', 'IntegrationInACVF.Section3ACVF.RVInverse.inverse']

ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.RVInputFibre.translate_mem_of_value', 'IntegrationInACVF.Section3ACVF.RVInputFibre.value_fibre_realized', 'IntegrationInACVF.Section3ACVF.RVSlopeGraph.relation_definable', 'IntegrationInACVF.Section3ACVF.RVSlopeGraph.multiply_rv', 'IntegrationInACVF.Section3ACVF.RVSlopeGraph.multiply_map_definable', 'IntegrationInACVF.Section3ACVF.RVSlopeGraph.slopes_definable', 'IntegrationInACVF.Section3ACVF.RVSlopeFibres.slope_of_pair', 'IntegrationInACVF.Section3ACVF.RVSlopeFibres.unique', 'IntegrationInACVF.Section3ACVF.RVIntegerOrbits.nat_value', 'IntegrationInACVF.Section3ACVF.RVIntegerOrbits.orbit_injective', 'IntegrationInACVF.Section3ACVF.RVIntegerOrbits.orbit_value', 'IntegrationInACVF.Section3ACVF.RVSlopeFiniteCofinite.row_definable', 'IntegrationInACVF.Section3ACVF.RVSlopeFiniteCofinite.finite_or_cofinite', 'IntegrationInACVF.Section3ACVF.RVSlopeOrbits.pair_orbit', 'IntegrationInACVF.Section3ACVF.RVSlopeOrbits.infinite', 'IntegrationInACVF.Section3ACVF.RVSlopeConstancy.on_value_fibre', 'IntegrationInACVF.Section3ACVF.RVSlopeGamma.sorted', 'IntegrationInACVF.Section3ACVF.RVSlopeGamma.graph_definable', 'IntegrationInACVF.Section3ACVF.RVSlopeGamma.finite_image', 'IntegrationInACVF.Section3ACVF.OpenBallSeparationGeometry.inside_value_lt_outside', 'IntegrationInACVF.Section3ACVF.InjectiveBallOrder.value_strictMono']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.RVSlopeGraph.relation', 'IntegrationInACVF.Section3ACVF.RVSlopeGraph.multiply', 'IntegrationInACVF.Section3ACVF.RVSlopeGraph.slopes', 'IntegrationInACVF.Section3ACVF.RVSlopeFiniteCofinite.row', 'IntegrationInACVF.Section3ACVF.RVSlopeGamma.relation']

HEADLINES += ['FiniteImageContinuity.locally_constant', 'FiniteImageContinuity.shift_locally_constant']
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.FiniteControllerLocal.constant_on_tail', 'IntegrationInACVF.Section3ACVF.GammaShiftConstancy.shift_constant', 'IntegrationInACVF.Section3ACVF.GammaShiftConstancy.radius_ratio', 'IntegrationInACVF.Section3ACVF.GammaDifferenceRealization.exists_pair', 'IntegrationInACVF.Section3ACVF.GammaDifferenceRealization.difference_gt_radius', 'IntegrationInACVF.Section3ACVF.GammaSlopeDomain.domain_iff', 'IntegrationInACVF.Section3ACVF.GammaSlopeDomain.coefficient_for_pair', 'IntegrationInACVF.Section3ACVF.GammaSlopeOutput.output_eq', 'IntegrationInACVF.Section3ACVF.GammaSlopeOutput.pair_output_value', 'IntegrationInACVF.Section3ACVF.FullGammaControllers.specialize', 'IntegrationInACVF.Section3ACVF.FullGammaControllers.finite_controller', 'IntegrationInACVF.Section3ACVF.FullGammaControllers.fix_last', 'IntegrationInACVF.Section3ACVF.GammaSlopeValueGraph.definable', 'IntegrationInACVF.Section3ACVF.GammaSlopeValueGraph.row_controller', 'IntegrationInACVF.Section3ACVF.GammaTailMap.coefficient_spec', 'IntegrationInACVF.Section3ACVF.GammaTailMap.valueMap_mem', 'IntegrationInACVF.Section3ACVF.GammaTailMap.strictMono', 'IntegrationInACVF.Section3ACVF.GammaTailIso.surjective', 'IntegrationInACVF.Section3ACVF.GammaTailIso.orderIso_val', 'IntegrationInACVF.Section3ACVF.GammaTailShift.shift_eq_coefficient', 'IntegrationInACVF.Section3ACVF.GammaTailShift.relation_shift', 'IntegrationInACVF.Section3ACVF.GammaTailShift.finite_range', 'IntegrationInACVF.Section3ACVF.GammaTailShift.row_controller', 'IntegrationInACVF.Section3ACVF.GammaTailShift.radius_ratio', 'IntegrationInACVF.Section3ACVF.GammaLinearity.ordinary', 'IntegrationInACVF.Section3ACVF.GammaLinearity.lemma_3_16']
DEFINITIONS += []
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.GammaSlopeValueGraph.valueRelation', 'IntegrationInACVF.Section3ACVF.GammaTailMap.coefficient', 'IntegrationInACVF.Section3ACVF.GammaTailMap.valueMap', 'IntegrationInACVF.Section3ACVF.GammaTailIso.orderIso', 'IntegrationInACVF.Section3ACVF.GammaLinearity.GammaLinear']

ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.SaturatedInterpretedFamilies.union_definable', 'IntegrationInACVF.Section3ACVF.SaturatedInterpretedFamilies.exists_nonalgebraic', 'IntegrationInACVF.Section3ACVF.SaturatedBallFamilies.exists_nonalgebraic', 'IntegrationInACVF.Section3ACVF.BetaSubballFamilies.gamma_subball_subset', 'IntegrationInACVF.Section3ACVF.BetaSubballFamilies.definable', 'IntegrationInACVF.Section3ACVF.BetaSubballFamilies.member_presentation', 'IntegrationInACVF.Section3ACVF.BetaSubballFamilies.cover', 'IntegrationInACVF.Section3ACVF.BetaSubballFamilies.infinite', 'IntegrationInACVF.Section3ACVF.BetaSubballFamilies.disjoint', 'IntegrationInACVF.Section3ACVF.NamedBallSetup.gamma_scalar_of_code', 'IntegrationInACVF.Section3ACVF.NamedBallSetup.cosetBody_definable', 'IntegrationInACVF.Section3ACVF.NamedBallSetup.gammaBall_definable', 'IntegrationInACVF.Section3ACVF.AtomicBallFamilyChoice.identity_graph', 'IntegrationInACVF.Section3ACVF.AtomicBallFamilyChoice.atomic_of_nonalgebraic', 'IntegrationInACVF.Section3ACVF.AtomicBallFamilyChoice.exists_atomic', 'IntegrationInACVF.Section3ACVF.LocalGammaLinearity.at_named_radius', 'IntegrationInACVF.Section3ACVF.LinearSubballSpecialization.inside_open_ball', 'IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.ballAt_gamma', 'IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.ballAt_infinity', 'IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.exists_at_radius', 'IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.corollary_3_17']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.SaturatedInterpretedFamilies.union', 'IntegrationInACVF.Section3ACVF.BetaSubballFamilies.family', 'IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.ballAt', 'IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.LinearOnRadius', 'IntegrationInACVF.Section3ACVF.LinearRadiusThreshold.IsLeastLinearRadius']

ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.RVValueShellGeometry.shell_mem', 'IntegrationInACVF.Section3ACVF.RVValueShellGeometry.gammaBall_eq_fibre', 'IntegrationInACVF.Section3ACVF.RVValueShellGeometry.gammaBall_subset_shell', 'IntegrationInACVF.Section3ACVF.RVValueShellGeometry.rv_image_infinite', 'IntegrationInACVF.Section3ACVF.RVValueBallFamilies.definable', 'IntegrationInACVF.Section3ACVF.RVValueBallFamilies.member_fibre', 'IntegrationInACVF.Section3ACVF.RVValueBallFamilies.cover', 'IntegrationInACVF.Section3ACVF.RVValueBallFamilies.infinite', 'IntegrationInACVF.Section3ACVF.RVValueBallFamilies.exists_atomic_fibre', 'IntegrationInACVF.Section3ACVF.RVUnaryConstancy.graph_eq', 'IntegrationInACVF.Section3ACVF.RVUnaryConstancy.constant', 'IntegrationInACVF.Section3ACVF.RVErrorComparison.error_value_gt', 'IntegrationInACVF.Section3ACVF.RVErrorComparison.affine_difference', 'IntegrationInACVF.Section3ACVF.RVSlopeControllers.row_definable', 'IntegrationInACVF.Section3ACVF.RVSlopeControllers.row_controller', 'IntegrationInACVF.Section3ACVF.FiniteControllerTails.eventual_label', 'IntegrationInACVF.Section3ACVF.RVSlopeTail.eventual_relation', 'IntegrationInACVF.Section3ACVF.RVSlopeTail.eventual_coefficient', 'IntegrationInACVF.Section3ACVF.RVErrorSyntax.poly_value', 'IntegrationInACVF.Section3ACVF.RVErrorSyntax.error_vf', 'IntegrationInACVF.Section3ACVF.RVErrorSyntax.error_definable', 'IntegrationInACVF.Section3ACVF.RVErrorSyntax.graph_definable', 'IntegrationInACVF.Section3ACVF.RVErrorConstancy.constant']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.RVValueShellGeometry.fibre', 'IntegrationInACVF.Section3ACVF.RVValueShellGeometry.shell', 'IntegrationInACVF.Section3ACVF.RVValueBallFamilies.family', 'IntegrationInACVF.Section3ACVF.RVUnaryConstancy.family', 'IntegrationInACVF.Section3ACVF.RVErrorSyntax.expression', 'IntegrationInACVF.Section3ACVF.RVErrorSyntax.polyTerm', 'IntegrationInACVF.Section3ACVF.RVErrorSyntax.affineError']

ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.VFExchangeAnyBase.parameterField_union_image', 'IntegrationInACVF.Section3ACVF.VFExchangeAnyBase.algebraic_iff_matroid_closure', 'IntegrationInACVF.Section3ACVF.VFExchangeAnyBase.exchange', 'IntegrationInACVF.Section3ACVF.FiniteFibresFromExchange.output_algebraic', 'IntegrationInACVF.Section3ACVF.FiniteFibresFromExchange.inverse_algebraic', 'IntegrationInACVF.Section3ACVF.FiniteFibresFromExchange.finite_fibres', 'IntegrationInACVF.Section3ACVF.AtomicFunctionFibres.no_algebraic_point', 'IntegrationInACVF.Section3ACVF.AtomicFunctionFibres.constant_or_finite_fibres', 'IntegrationInACVF.Section3ACVF.FiniteFibreInjectivity.injOn_of_centred_RV_constant', 'IntegrationInACVF.Section3ACVF.FiniteFibreInjectivity.centred_graph_definable', 'IntegrationInACVF.Section3ACVF.FiniteFibreInjectivity.injOn_of_definable_fibre_mean', 'IntegrationInACVF.Section3ACVF.FullFibreEnumerations.exists_finite', 'IntegrationInACVF.Section3ACVF.FullFibreEnumerations.definable', 'IntegrationInACVF.Section3ACVF.FullFibreMeans.equation_definable', 'IntegrationInACVF.Section3ACVF.FullFibreMeans.graphAt_definable', 'IntegrationInACVF.Section3ACVF.FullFibreMeans.normalized_mean_equation', 'IntegrationInACVF.Section3ACVF.FullFibreMeans.graphAt_value', 'IntegrationInACVF.Section3ACVF.FullFibreMeans.mean_mem_graphAt', 'IntegrationInACVF.Section3ACVF.FullFibreMeans.bounded_graph_definable', 'IntegrationInACVF.Section3ACVF.AtomicFibreMeanGraph.exists_mean_graph', 'IntegrationInACVF.Section3ACVF.AtomicFunctionInjectivity.constant_or_injective', 'IntegrationInACVF.Section3ACVF.AtomicValueBoundRigidity.impossible', 'IntegrationInACVF.Section3ACVF.RVLeadingDifference.value_sub', 'IntegrationInACVF.Section3ACVF.RVLinearitySlopeValues.coefficient_value', 'IntegrationInACVF.Section3ACVF.RVLinearitySlopeValues.lift_value', 'IntegrationInACVF.Section3ACVF.RVSlopePairFormula.multiply_difference', 'IntegrationInACVF.Section3ACVF.RVSlopePairFormula.pair_eq', 'IntegrationInACVF.Section3ACVF.RVSlopePairFormula.pair_ne', 'IntegrationInACVF.Section3ACVF.RealGraphOperations.postcompose', 'IntegrationInACVF.Section3ACVF.VFErrorSyntax.fieldError_vf', 'IntegrationInACVF.Section3ACVF.VFErrorSyntax.fieldError_definable', 'IntegrationInACVF.Section3ACVF.TranslationSyntax.input_vf', 'IntegrationInACVF.Section3ACVF.TranslationSyntax.graph_definable', 'IntegrationInACVF.Section3ACVF.TranslationSyntax.translate_mem', 'IntegrationInACVF.Section3ACVF.RealAtomicValueBoundRigidity.impossible', 'IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry.transformed_vf', 'IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry.graph_definable', 'IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry.strict_value', 'IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry.pair_value', 'IntegrationInACVF.Section3ACVF.RVSlopeRigidity.ordered_coefficients_eq', 'IntegrationInACVF.Section3ACVF.RVLinearity.ordinary_lift', 'IntegrationInACVF.Section3ACVF.RVLinearity.ordinary', 'IntegrationInACVF.Section3ACVF.RVLinearity.lemma_3_18']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.FullFibreMeans.equation', 'IntegrationInACVF.Section3ACVF.FullFibreMeans.graphAt', 'IntegrationInACVF.Section3ACVF.VFErrorSyntax.fieldError', 'IntegrationInACVF.Section3ACVF.TranslationSyntax.input', 'IntegrationInACVF.Section3ACVF.TranslationSyntax.domain', 'IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry.transformed', 'IntegrationInACVF.Section3ACVF.RVLinearity.RVLinear']

ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.CompleteTypeRVProfiles.presentation', 'IntegrationInACVF.Section3ACVF.CompleteTypeRVProfiles.constant_on_open_ball', 'IntegrationInACVF.Section3ACVF.SelfCentredBallProfiles.definable', 'IntegrationInACVF.Section3ACVF.SelfCentredBallProfiles.centre_change', 'IntegrationInACVF.Section3ACVF.SelfCentredBallProfiles.decode_self', 'IntegrationInACVF.Section3ACVF.SelfCentredBallProfiles.profile_mem', 'IntegrationInACVF.Section3ACVF.OpenCompleteTypeAtomicity.atomic_open_of_infinite_complete_type', 'IntegrationInACVF.Section3ACVF.OpenCompleteTypeAtomicity.lemma_3_4_open_gamma_base', 'IntegrationInACVF.Section3ACVF.CompleteTypeOpenImages.complete_type_not_contains_vf', 'IntegrationInACVF.Section3ACVF.CompleteTypeOpenImages.ordinary_gamma_base', 'IntegrationInACVF.Section3ACVF.CompleteTypeOpenImages.lemma_3_15_gamma_base']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.SelfCentredBallProfiles.selfCode', 'IntegrationInACVF.Section3ACVF.SelfCentredBallProfiles.profile']

HEADLINES += ['FiniteFieldDefinableMaps.power_fixed_iff_range', 'FiniteFieldDefinableMaps.definable_invariant', 'FiniteFieldDefinableMaps.mapsTo_finite_subfield', 'LocallyFiniteDefinableInjection.surjOn_of_injOn', 'LocallyFiniteRelations.every_input_has_predecessor', 'DefinableInjectionSentence.realize_row', 'DefinableInjectionSentence.realize_equalRows', 'DefinableInjectionSentence.realize_successor', 'DefinableInjectionSentence.realize_predecessor', 'DefinableInjectionSentence.realize_scheme', 'ACFDefinableInjection.locally_finite_scheme', 'ACFDefinableInjection.models_scheme_prime', 'ACFDefinableInjection.models_scheme', 'ACFDefinableInjection.surjOn_of_injOn', 'FiniteDefinablePatching.singleton_univ', 'FiniteDefinablePatching.finite_univ', 'CofiniteDefinableInjection.deficit_le', 'CofiniteDefinableInjection.finite_image_complement', 'CofiniteDefinableBijection.complements_card_eq']
DEFINITIONS += ['DefinableInjectionSentence.row', 'DefinableInjectionSentence.equalRows', 'DefinableInjectionSentence.successor', 'DefinableInjectionSentence.predecessor', 'DefinableInjectionSentence.scheme']

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


HEADLINES += ['FiniteTupleGraphs.comp', 'FiniteTupleGraphs.inverse', 'TaggedLineMaps.mapsTo', 'TaggedLineMaps.injOn', 'TaggedLineMaps.graph_definable', 'TaggedLineMaps.missing_line_infinite', 'TaggedLineMaps.surjOn', 'TaggedCofiniteConservation.components_le', 'TaggedCofiniteConservation.components_and_holes']
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.ResidueFieldConservation.residue_pullback_definable', 'IntegrationInACVF.Section3ACVF.ResidueFieldConservation.graph_definable', 'IntegrationInACVF.Section3ACVF.ResidueFieldConservation.cofinite_bijection_card', 'IntegrationInACVF.Section3ACVF.ResidueTaggedConservation.components_and_holes']
DEFINITIONS += ['FiniteTupleGraphs.graph', 'TaggedLineMaps.space', 'TaggedLineMaps.transport']

HEADLINES += ['AffineResidueChart.div_integral', 'AffineResidueChart.surjective', 'AffineResidueChart.same_fibres', 'AffineResidueChart.open_subset_closed', 'AffineResidueChart.fibre_set']
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.BallResidueChart.representative_ne_zero', 'IntegrationInACVF.Section3ACVF.BallResidueChart.surjective', 'IntegrationInACVF.Section3ACVF.BallResidueChart.same_fibres', 'IntegrationInACVF.Section3ACVF.BallResidueChart.fibre_set', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.centre_coordinate', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.underlying_ball', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.mem_ball', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.underlying_injective', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.ball_injective', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.ball_coordinate', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.range_ball', 'IntegrationInACVF.Section3ACVF.ResiduePunctures.hole_coordinate', 'IntegrationInACVF.Section3ACVF.ResiduePunctures.finite_holes']
DEFINITIONS += ['AffineResidueChart.closed', 'AffineResidueChart.integral', 'AffineResidueChart.chart']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.BallResidueChart.Point', 'IntegrationInACVF.Section3ACVF.BallResidueChart.fieldPoint', 'IntegrationInACVF.Section3ACVF.BallResidueChart.coordinate', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.centre', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.ball', 'IntegrationInACVF.Section3ACVF.ResidueBallClasses.family']

HEADLINES += ['SurjectiveQuotientMap.exists_bijective_factor']
ACVF_HEADLINES += ['IntegrationInACVF.Section3ACVF.CanonicalModelEquality.normalize_eq', 'IntegrationInACVF.Section3ACVF.ResidueReductionSyntax.formula_realize', 'IntegrationInACVF.Section3ACVF.ResidueReductionSyntax.rawGraph_definable', 'IntegrationInACVF.Section3ACVF.ResidueReductionSyntax.residue_iff', 'IntegrationInACVF.Section3ACVF.ResidueReductionSyntax.rawGraph_iff', 'IntegrationInACVF.Section3ACVF.ResidueReductionSyntax.coordinate_iff', 'IntegrationInACVF.Section3ACVF.AffineResidueSyntax.graph_definable', 'IntegrationInACVF.Section3ACVF.AffineResidueSyntax.coordinate_iff', 'IntegrationInACVF.Section3ACVF.ThinFamilyGeometry.covered_ball_parent', 'IntegrationInACVF.Section3ACVF.ThinFamilyGeometry.open_subset_class', 'IntegrationInACVF.Section3ACVF.MaximalOpenClasses.class_maximal', 'IntegrationInACVF.Section3ACVF.MaximalOpenClasses.maximal_is_class', 'IntegrationInACVF.Section3ACVF.MaximalOpenClasses.image_maximal', 'IntegrationInACVF.Section3ACVF.OpenToOpenQuotient.maximal_eq_of_inter', 'IntegrationInACVF.Section3ACVF.OpenToOpenQuotient.same_fibres']
ACVF_DEFINITIONS += ['IntegrationInACVF.Section3ACVF.ResidueReductionSyntax.rawGraph', 'IntegrationInACVF.Section3ACVF.ResidueReductionSyntax.formula', 'IntegrationInACVF.Section3ACVF.AffineResidueSyntax.graph', 'IntegrationInACVF.Section3ACVF.ThinFamilyGeometry.IsThin', 'IntegrationInACVF.Section3ACVF.ThinFamilyGeometry.body', 'IntegrationInACVF.Section3ACVF.MaximalOpenClasses.IsMaximal', 'IntegrationInACVF.Section3ACVF.MaximalOpenClasses.OpenToOpen', 'IntegrationInACVF.Section3ACVF.OpenToOpenQuotient.fibre']

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
            + 'import IntegrationSection3.FieldLibrary\n'
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
                         'definable Gamma radii, singletons and VF; Lemmas 3.6, 3.8, corrected 3.11, both consequences of 3.12 and Lemma 3.13 over the full base; Lemma3.14 with only the source ball imaginary and original Gamma names; all with ACVF(0,0) and a definable nontrivial Gamma value explicit; actual finite disjoint punctured '
                         'decomposition; finite coset-profile exceptions, Lemma 3.9 and Corollary 3.10 with the sequel open-ball convention and domain graphs; ' if args.acvf else '')
                      + 'RV difference bijection, integer equivariance, constancy of RV coefficients on value fibres and strict valuation-order preservation for atomic open-ball maps are checked; full-code Gamma slope descent and finite image are checked with genuine saturation and small-real-base hypotheses for finite image; Lemma 3.16 Gamma-linearity with radius ratio is proved over the full original base, with genuine saturation, infinite saturation cardinal and small real base explicit; Corollary 3.17 is proved for every given least-radius function, including VF source, with actual linear subball existence at every smaller ordinary radius; Lemma 3.18 actual RV-linearity is proved over the full original base, with genuine saturation, infinite cardinal, small real base, ACVF00 and named nontrivial Gamma value explicit. Finite-fibre means prove error-map injectivity on a newly chosen atomic RV fibre; checked 3.16 supplies the radius contradiction. No endpoint estimate, error-injectivity premise or unproved external input is assumed; unnamed-radius open-ball 3.4 and Lemma 3.15 are additionally proved over real/Gamma bases even for a possibly undefinable ambient complete-type set. A pure-field definable injective self-map is proved surjective by finite-field Frobenius and ACF transfer; finite patching proves conservation of finite complements of cofinite definable bijections. These are pure-field components for 3.22, not a native ball-quotient proof. The extension with old ball parameters, unrestricted Lemma 3.15 and results 3.19, 3.21-3.24 remain open'),
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
