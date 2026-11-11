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
    'IntegrationInACVF.Section5.contractible_comp',
    'IntegrationInACVF.Section5.focus_post_contractible',
    'IntegrationInACVF.Section5.focused_post_contractible',
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
    'IntegrationInACVF.Section5.unaryShift_zero',
    'IntegrationInACVF.Section5.matched_focus_contractible',
    'IntegrationInACVF.Section5.matched_focus_zero_preimages',
    'IntegrationInACVF.Section5.matched_focus_reverse_contractible',
    'IntegrationInACVF.Section5.lemma_5_1_real_base',
    'IntegrationInACVF.Section5.prepared_inverse_open_images',
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
    'IntegrationInACVF.Section5.canonical_contractible',
    'IntegrationInACVF.Section5.canonical_eq_reframe',
    'IntegrationInACVF.Section5.canonical_open_images',
    'IntegrationInACVF.Section5.inverse_keycell_image',
    'IntegrationInACVF.Section5.CellwiseOpenEquivalence',
    'IntegrationInACVF.Section5.cellwiseOpenEquivalence_open',
    'IntegrationInACVF.Section5.unaryImage_inverse_apply',
    'IntegrationInACVF.Section5.unaryImage_apply_inverse',
    'IntegrationInACVF.Section5.cellwiseOpenEquivalence_inverse',
    'IntegrationInACVF.Section5.inverse_special_open_iff',
    'IntegrationInACVF.Section5.unaryConjugate',
    'IntegrationInACVF.Section5.unaryConjugate_bijective',
    'IntegrationInACVF.Section5.unaryConjugate_image',
    'IntegrationInACVF.Section5.cellwiseOpenEquivalence_conjugate',
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
    'IntegrationInACVF.Section5.unary_focus_center_eq',
    'IntegrationInACVF.Section5.focusClassShift',
    'IntegrationInACVF.Section5.unary_focus_eta_eq_shift',
    'IntegrationInACVF.Section5.unary_focus_image_eq_shift',
    'IntegrationInACVF.Section5.focus_primitive_open_images',
    'IntegrationInACVF.Section5.focussedCanonical',
    'IntegrationInACVF.Section5.focussedCanonical_vf',
    'IntegrationInACVF.Section5.inverse_special_labels',
    'IntegrationInACVF.Section5.inverse_special_difference',
    'IntegrationInACVF.Section5.inverse_special_affine',
    'IntegrationInACVF.Section5.inverse_special_image_eq',
    'IntegrationInACVF.Section5.inverse_special_open_images',
    'IntegrationInACVF.Section5.unaryImage',
    'IntegrationInACVF.Section5.unaryImage_subset',
    'IntegrationInACVF.Section5.unaryImage_comp',
    'IntegrationInACVF.Section5.unaryImage_congr',
    'IntegrationInACVF.Section5.CellwiseOpenMap',
    'IntegrationInACVF.Section5.cellwiseOpenMap_comp',
    'IntegrationInACVF.Section5.unaryReframe',
    'IntegrationInACVF.Section5.unaryReframe_open_polydisc',
    'IntegrationInACVF.Section5.unaryReframe_open_iff',
    'IntegrationInACVF.Section5.unary_focus_preserves_zero',
    'IntegrationInACVF.Section5.unary_primitive_preserves_zero',
    'IntegrationInACVF.Section5.unary_chain_preserves_zero',
    'IntegrationInACVF.Section5.unary_special_preserves_zero',
    'IntegrationInACVF.Section5.unary_focus_section_zero',
    'IntegrationInACVF.Section5.unary_tail_focus_section_zero',
    'IntegrationInACVF.Section5.unaryShift',
    'IntegrationInACVF.Section5.unaryShift_injective',
    'IntegrationInACVF.Section5.unaryShift_add_cancel',
    'IntegrationInACVF.Section5.unaryShift_open_polydisc',
    'IntegrationInACVF.Section5.unaryShift_eq_zero_iff',
    'IntegrationInACVF.Section5.unaryConjugate_inverse',
    'IntegrationInACVF.Section5.special_split_inverse',
    'IntegrationInACVF.Section5.conjugate_tail_inverse',
    'IntegrationInACVF.Section5.conjugate_tail_contractible',
    'IntegrationInACVF.Section5.special_comp_apply',
    'IntegrationInACVF.Section5.special_comp_inverse',
    'IntegrationInACVF.Section5.special_refl_inverse',
    'IntegrationInACVF.Section5.gamma_chain_append',
    'IntegrationInACVF.Section5.gamma_focussedCanonical',
    'IntegrationInACVF.Section5.gamma_unaryConjugate_graph',
    'IntegrationInACVF.Section5.replacementGraphMap',
    'IntegrationInACVF.Section5.replacementGraphMap_apply',
    'IntegrationInACVF.Section5.gamma_focusSection_graph',
    'IntegrationInACVF.Section5.gammaPointCode_injective',
    'IntegrationInACVF.Section5.gammaGraph_inter',
    'IntegrationInACVF.Section5.gamma_inverse_map_graph',
    'IntegrationInACVF.Section5.gamma_map_preimage',
    'IntegrationInACVF.Section5.gamma_sameRV_graph',
    'IntegrationInACVF.Section5.gamma_matched_chain_induction',
    'IntegrationInACVF.Section5.gamma_prepared_bijective_contraction',
    'IntegrationInACVF.Section5.gamma_pulledFocusSection_graph',
    'IntegrationInACVF.Section5.gamma_pulledFocusLocus',
    'IntegrationInACVF.Section5.unaryVFPointProjection',
    'IntegrationInACVF.Section5.gamma_pulledFocus',
    'IntegrationInACVF.Section5.matched_chain_induction',
    'IntegrationInACVF.Section5.focussedCanonical_alternating',
    'IntegrationInACVF.Section5.focussedCanonical_lastKind',
    'IntegrationInACVF.Section5.focussedCanonical_tagged',
    'IntegrationInACVF.Section5.matched_focus_step',
    'IntegrationInACVF.Section5.prepared_mutual_contraction',
    'IntegrationInACVF.Section5.prepared_bijective_contraction',
    'IntegrationInACVF.Section5.unaryInsert',
    'IntegrationInACVF.Section5.vfShadow',
    'IntegrationInACVF.Section5.ordinaryRawOpen',
    'IntegrationInACVF.Section5.unaryInsert_shadow',
    'IntegrationInACVF.Section5.gammaBall_eq_ordinaryRawOpen',
    'IntegrationInACVF.Section5.ordinaryRawOpen_paper_open',
    'IntegrationInACVF.Section5.paper_open_ordinary',
    'IntegrationInACVF.Section5.vfShadow_polydisc_iff',
    'IntegrationInACVF.Section5.vfShadow_ne_whole_of_cell',
    'IntegrationInACVF.Section5.unaryConjugate_comp',
    'IntegrationInACVF.Section5.family_gamma_real_presentation',
    'IntegrationInACVF.Section5.gammaFullBase',
    'IntegrationInACVF.Section5.gamma_to_full',
    'IntegrationInACVF.Section5.full_to_gamma',
    'IntegrationInACVF.Section5.pointRelationIndex',
    'IntegrationInACVF.Section5.pointRelationValues_eq_code',
    'IntegrationInACVF.Section5.gammaGraph_full_raw',
    'IntegrationInACVF.Section5.unaryTupleMap_graph',
    'IntegrationInACVF.Section5.unaryTupleMap_injective',
    'IntegrationInACVF.Section5.gamma_membershipMap_graph',
    'IntegrationInACVF.Section5.gamma_prepare_finite_maps_at_boundary',
    'IntegrationInACVF.Section5.gamma_prepare_finite_membership_at_boundary',
    'IntegrationInACVF.Section5.gamma_prepare_finite_membership',
    'IntegrationInACVF.Section5.gamma_open_preparation_from_partition',
    'IntegrationInACVF.Section5.pointValues_eq_gammaPointCode',
    'IntegrationInACVF.Section5.pointValues_image_iff',
    'IntegrationInACVF.Section5.gammaPointCode_sorted',
    'IntegrationInACVF.Section5.gammaSet_full_raw_iff',
    'IntegrationInACVF.Section5.gamma_prepared_bijective_contraction_at_boundary',
    'IntegrationInACVF.Section5.prepared_coordinate_partition',
    'IntegrationInACVF.Section5.gamma_tagged_tail',
    'IntegrationInACVF.Section5.lemma_5_2',
    'IntegrationInACVF.Section5.unary_bijection_from_partition',
    'IntegrationInACVF.Section5.lemma_5_2_gamma_presented',
    'IntegrationInACVF.Section5.pointValues_injective',
    'IntegrationInACVF.Section5.unaryTupleMap',
    'IntegrationInACVF.Section5.unaryTupleMap_apply',
    'IntegrationInACVF.Section5.pointValues_tail_eq',
    'IntegrationInACVF.Section5.unaryTuple_insert',
    'IntegrationInACVF.Section5.coordinate_shadow_image',
    'IntegrationInACVF.Section5.coordinate_piece_open_iff',
    'IntegrationInACVF.Section5.coordinate_open_to_cellwise',
    'IntegrationInACVF.Section5.refined_coordinate_open_to_cellwise',
    'IntegrationInACVF.Section5.refined_conjugate_coordinate_geometry',
    'IntegrationInACVF.Section5.unary_coordinate_partition',
    'IntegrationInACVF.Section5.inverse_map_bijective',
    'IntegrationInACVF.Section5.inverse_map_inverse_apply',
    'IntegrationInACVF.Section5.inverse_map_inverse_contractible',
    'IntegrationInACVF.Section5.mixedKeyPoint',
    'IntegrationInACVF.Section5.mixedKeyPointMap',
    'IntegrationInACVF.Section5.gamma_key_relation',
    'IntegrationInACVF.Section5.gamma_rvContractionMap_graph',
    'IntegrationInACVF.Section5.rawKeyMap_eq_iff',
    'IntegrationInACVF.Section5.rvContractionMap',
    'IntegrationInACVF.Section5.rvContractionMap_spec',
    'IntegrationInACVF.Section5.rawKeyImage_surjective',
    'IntegrationInACVF.Section5.rvContractionMap_bijective',
    'IntegrationInACVF.Section5.pullbackObject_value_key',
    'IntegrationInACVF.Section5.rvContractionMap_volume_spec',
    'IntegrationInACVF.Section5.rvWeight_unary',
    'IntegrationInACVF.Section5.rvWeight_unary_tuple',
    'IntegrationInACVF.Section5.nonzero_rv_cell_another',
    'IntegrationInACVF.Section5.unary_bijection_maps_zero',
    'IntegrationInACVF.Section5.unary_bijection_zero_iff',
    'IntegrationInACVF.Section5.rvPullbackMapGraph',
    'IntegrationInACVF.Section5.unaryIsoHomMap',
    'IntegrationInACVF.Section5.unaryIsoInvMap',
    'IntegrationInACVF.Section5.lemma_5_3',
    'IntegrationInACVF.Section5.rvContractionMap_volumetric',
    'IntegrationInACVF.Section5.unaryRVHom',
    'IntegrationInACVF.Section5.unaryRVIso',
    'IntegrationInACVF.Section5.unaryRVIso_spec',
    'IntegrationInACVF.Section5.unary_vf_fibre_image_finite',
    'IntegrationInACVF.Section5.unary_vf_fibre_image_finite_typed',
    'IntegrationInACVF.Section5.rvContractionMap_finite_volume_images',
    'IntegrationInACVF.Section5.coordinateInsert',
    'IntegrationInACVF.Section5.coordinateProject',
    'IntegrationInACVF.Section5.coordinateProject_insert',
    'IntegrationInACVF.Section5.coordinateInsert_project',
    'IntegrationInACVF.Section5.coordinateInsert_injective',
    'IntegrationInACVF.Section5.coordinateInsert_sameRV',
    'IntegrationInACVF.Section5.coordinateFibreBase',
    'IntegrationInACVF.Section5.coordinateInsertMap',
    'IntegrationInACVF.Section5.coordinateProjectMap',
    'IntegrationInACVF.Section5.coordinateFibre',
    'IntegrationInACVF.Section5.mapIntoSubset',
    'IntegrationInACVF.Section5.coordinateFibreEmbedding',
    'IntegrationInACVF.Section5.coordinateFibreEmbedding_apply',
    'IntegrationInACVF.Section5.coordinateInsert_other',
    'IntegrationInACVF.Section5.coordinateFibreMap',
    'IntegrationInACVF.Section5.coordinateFibreMap_apply',
    'IntegrationInACVF.Section5.coordinateFibreMap_insert',
    'IntegrationInACVF.Section5.coordinateFibreMap_bijective',
    'IntegrationInACVF.Section5.coordinateInsert_replace',
    'IntegrationInACVF.Section5.fibreFocusLocus',
    'IntegrationInACVF.Section5.fibreFocusLocus_pullback',
    'IntegrationInACVF.Section5.fibreFocusGeometry',
    'IntegrationInACVF.Section5.fibreFocusGeometry_eta_insert',
    'IntegrationInACVF.Section5.fibreFocusLocus_definable',
    'IntegrationInACVF.Section5.fibreFocusActive',
    'IntegrationInACVF.Section5.fibreFocusActiveEmbedding',
    'IntegrationInACVF.Section5.fibreFocusCentreMap',
    'IntegrationInACVF.Section5.fibreFocusCentre_graph',
    'IntegrationInACVF.Section5.fibreFocus',
    'IntegrationInACVF.Section5.fibreFocus_image_carrier',
    'IntegrationInACVF.Section5.fibreFocus_image_eq',
    'IntegrationInACVF.Section5.specialCastTarget',
    'IntegrationInACVF.Section5.specialCastTarget_val',
    'IntegrationInACVF.Section5.fibreCentripetal',
    'IntegrationInACVF.Section5.fibreCentripetal_apply',
    'IntegrationInACVF.Section5.SpecialRelative',
    'IntegrationInACVF.Section5.RelativelySpecial',
    'IntegrationInACVF.Section5.specialRelative_unaryRelative',
    'IntegrationInACVF.Section5.specialRelative_id',
    'IntegrationInACVF.Section5.centripetal_unaryRelative',
    'IntegrationInACVF.Section5.centripetal_specialRelative',
    'IntegrationInACVF.Section5.centripetal_relativelySpecial',
    'IntegrationInACVF.Section5.coordinateCanonical',
    'IntegrationInACVF.Section5.coordinateCanonicalCodes',
    'IntegrationInACVF.Section5.coordinateCanonicalMap',
    'IntegrationInACVF.Section5.coordinateCanonicalImage',
    'IntegrationInACVF.Section5.coordinateCanonicalBijection',
    'IntegrationInACVF.Section5.coordinateCanonical_injective',
    'IntegrationInACVF.Section5.coordinateCanonicalBijection_bijective',
    'IntegrationInACVF.Section5.coordinateCanonical_unaryRelative',
    'IntegrationInACVF.Section5.coordinateInsert_canonical',
    'IntegrationInACVF.Section5.coordinateCanonical_fibre_carrier',
    'IntegrationInACVF.Section5.coordinateCanonical_fibre_eq',
    'IntegrationInACVF.Section5.coordinateCanonicalFibre',
    'IntegrationInACVF.Section5.coordinateCanonical_specialRelative',
    'IntegrationInACVF.Section5.RelativeSpecialChain',
    'IntegrationInACVF.Section5.RelativeSpecialChain.toMap',
    'IntegrationInACVF.Section5.RelativeSpecialChain.bijective',
    'IntegrationInACVF.Section5.RelativeSpecialChain.append',
    'IntegrationInACVF.Section5.RelativeSpecialChain.append_toMap',
    'IntegrationInACVF.Section5.RelativeSpecialChain.castTarget',
    'IntegrationInACVF.Section5.RelativeSpecialChain.castTarget_val',
    'IntegrationInACVF.Section5.pointRVList',
    'IntegrationInACVF.Section5.coordinateCanonical_sequence',
    'IntegrationInACVF.Section5.canonical_relativeSpecial_factorization',
    'IntegrationInACVF.Section5.primitive_relativeSpecial_factorization',
    'IntegrationInACVF.Section5.chain_relativeSpecial_factorization',
    'IntegrationInACVF.Section5.special_relativeSpecial_factorization',
    'IntegrationInACVF.Section5.coordinateGammaBase',
    'IntegrationInACVF.Section5.gammaSet_mono_real',
    'IntegrationInACVF.Section5.gammaGraph_mono_real',
    'IntegrationInACVF.Section5.gamma_coordinate_preimage',
    'IntegrationInACVF.Section5.gamma_coordinateFibre',
    'IntegrationInACVF.Section5.gamma_coordinateFibreMap',
    'IntegrationInACVF.Section5.gamma_fibreFocus',
    'IntegrationInACVF.Section5.coordinateCanonical_preserves_pullback',
    'IntegrationInACVF.Section5.fibreFocus_map_image_carrier',
    'IntegrationInACVF.Section5.specialRelative_of_fibre_focus',
    'IntegrationInACVF.Section5.specialRelativeBoundary_of_fibre_focus',
    'IntegrationInACVF.Section5.specialRelative_headSaturated',
    'IntegrationInACVF.Section5.coordinateCanonical_tagged',
    'IntegrationInACVF.Section5.verticalMeanMap_specialRelativeBoundary',
    'IntegrationInACVF.Section5.verticalMeanStepTarget',
    'IntegrationInACVF.Section5.verticalMeanStepMap',
    'IntegrationInACVF.Section5.verticalMeanStep_boundary',
    'IntegrationInACVF.Section5.verticalMeanStep_headSaturated',
    'IntegrationInACVF.Section5.coordinateCanonical_headKey',
    'IntegrationInACVF.Section5.headSaturated_iff_coordinateFibre',
    'IntegrationInACVF.Section5.coordinateCanonical_image_headLift',
    'IntegrationInACVF.Section5.HeadPreparation',
    'IntegrationInACVF.Section5.HeadPreparation.bijective',
    'IntegrationInACVF.Section5.HeadPreparation.contractedSet',
    'IntegrationInACVF.Section5.HeadPreparation.contractionMap',
    'IntegrationInACVF.Section5.HeadPreparation.liftSet',
    'IntegrationInACVF.Section5.HeadPreparation.liftMap',
    'IntegrationInACVF.Section5.HeadPreparation.liftMap_bijective',
    'IntegrationInACVF.Section5.HeadPreparation.contractionMap_surjective',
    'IntegrationInACVF.Section5.HeadPreparation.lifting_square',
    'IntegrationInACVF.Section5.HeadPreparation.liftSet_exact',
    'IntegrationInACVF.Section5.HeadPreparation.contractionMap_eq_iff',
    'IntegrationInACVF.Section5.OrderedContractionProgram',
    'IntegrationInACVF.Section5.OrderedContractionProgram.toMap',
    'IntegrationInACVF.Section5.OrderedContractionProgram.surjective',
    'IntegrationInACVF.Section5.OrderedContractionProgram.rvArity_le',
    'IntegrationInACVF.Section5.OrderedContractionProgram.oldLabels',
    'IntegrationInACVF.Section5.OrderedContractionProgram.volumeIndex',
    'IntegrationInACVF.Section5.OrderedContractionProgram.volumeIndex_before_oldLabels',
    'IntegrationInACVF.Section5.OrderedContractionProgram.volumeIndex_injective',
    'IntegrationInACVF.Section5.coordinateFibreMap_bijective_iff',
    'IntegrationInACVF.Section5.specialRelative_bijective',
    'IntegrationInACVF.Section5.relative_prepare_gamma_relation',
    'IntegrationInACVF.Section5.fibreSpecial_inverse_insert',
    'IntegrationInACVF.Section5.HeadPreparation.inverseMap',
    'IntegrationInACVF.Section5.HeadPreparation.inverse_apply',
    'IntegrationInACVF.Section5.HeadPreparation.apply_inverse',
    'IntegrationInACVF.Section5.HeadPreparation.inverse_tail',
    'IntegrationInACVF.Section5.HeadPreparation.inverse_labels',
    'IntegrationInACVF.Section5.HeadPreparation.inverse_difference',
    'IntegrationInACVF.Section5.HeadPreparation.inverseSlice',
    'IntegrationInACVF.Section5.HeadPreparation.inverse_pair',
    'IntegrationInACVF.Section5.HeadPreparation.inverse_slice',
    'IntegrationInACVF.Section5.special_chain_rvArity_le',
    'IntegrationInACVF.Section5.suffixIndex',
    'IntegrationInACVF.Section5.special_chain_labelIndex',
    'IntegrationInACVF.Section5.special_oldLabels',
    'IntegrationInACVF.Section5.specialRelative_rvArity_le',
    'IntegrationInACVF.Section5.specialRelative_oldLabels',
    'IntegrationInACVF.Section5.relative_zero_obstacles',
    'IntegrationInACVF.Section5.relative_prepare_realRV',
    'IntegrationInACVF.Section5.SpecialRelativeBoundary',
    'IntegrationInACVF.Section5.specialRelativeBoundary_forget',
    'IntegrationInACVF.Section5.mapComp_unaryRelative',
    'IntegrationInACVF.Section5.coordinateFibreMap_comp',
    'IntegrationInACVF.Section5.specialCastTarget_alternating',
    'IntegrationInACVF.Section5.specialCastTarget_lastKind',
    'IntegrationInACVF.Section5.specialRelativeBoundary_id',
    'IntegrationInACVF.Section5.coordinateCanonical_specialRelativeBoundary',
    'IntegrationInACVF.Section5.specialRelativeBoundary_comp',
    'IntegrationInACVF.Section5.verticalMeanCentre',
    'IntegrationInACVF.Section5.verticalMeanEta',
    'IntegrationInACVF.Section5.verticalMeanActive',
    'IntegrationInACVF.Section5.verticalMeanInactive',
    'IntegrationInACVF.Section5.verticalMeanActiveMap',
    'IntegrationInACVF.Section5.verticalMeanInactiveMap',
    'IntegrationInACVF.Section5.verticalMeanActiveMap_apply',
    'IntegrationInACVF.Section5.verticalMeanInactiveMap_apply',
    'IntegrationInACVF.Section5.verticalMeanMap',
    'IntegrationInACVF.Section5.verticalMeanMap_unaryRelative',
    'IntegrationInACVF.Section5.dropHead_coordinateInsert',
    'IntegrationInACVF.Section5.verticalMeanFibreFocus',
    'IntegrationInACVF.Section5.coordinateInsert_verticalMeanEta',
    'IntegrationInACVF.Section5.verticalMeanMap_specialRelative',
    'IntegrationInACVF.Section5.verticalParentBase',
    'IntegrationInACVF.Section5.verticalMeanStep_apply',
    'IntegrationInACVF.Section5.verticalMeanStep_fibre_subset',
    'IntegrationInACVF.Section5.verticalMeanStepFamily',
    'IntegrationInACVF.Section5.verticalMeanStep_bound',
    'IntegrationInACVF.Section5.verticalRoots_centralize',
    'IntegrationInACVF.Section5.verticalTail',
    'IntegrationInACVF.Section5.coordinateInsert_unaryPoint',
    'IntegrationInACVF.Section5.verticalRootFibre',
    'IntegrationInACVF.Section5.verticalRootFibre_fibre',
    'IntegrationInACVF.Section5.verticalRootFibre_bound',
    'IntegrationInACVF.Section5.coordinateFibre_tagged',
    'IntegrationInACVF.Section5.verticalRootFibre_hull',
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
            match = re.search(r'(?m)^@?' + re.escape(name) + r'(?:\.\{[^}]*\})?\s*:', output)
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
            'scope': 'Lemmas 5.1–5.2, Remark 5.3, Definition 5.4, exact relative-special factorization and genuine uniform relative preparation over the recorded real/Gamma base scope. Ordered contraction data are support; full 5.5–5.8 remain in progress. See STATUS.md for exact hypotheses and remaining Section5 targets.',
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
