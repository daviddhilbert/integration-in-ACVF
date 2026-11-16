module

public import Integration7.HKBasicGeneration
public import Integration7.HKBlowupUniversalProperty
public import Integration7.HKGradedBlowupProjection
public import Integration7.HKPositiveBasicGeneration
public import Integration7.HKPrincipalVolumeKernel
public import Integration7.HKRawVolumeKernelIdeal
public import Integration7.HKUpstreamRVZero
public import Integration7.HKUpstreamVFZero
public import Integration7.HKVolumeBlowupRelations
public import Integration7.HKVolumeBlowupSemiring
public import Integration7.HKVolumeClassCoherence
public import Integration7.HKVolumeClasses
public import Integration7.HKVolumeCoproductIsomorphisms
public import Integration7.HKVolumeCoproducts
public import Integration7.HKVolumeDataRelabeling
public import Integration7.HKVolumeIsoOperations
public import Integration7.HKVolumeIsoSemiring
public import Integration7.HKVolumeLeftDistributivity
public import Integration7.HKVolumeProductAssociativity
public import Integration7.HKVolumeProductUnits
public import Integration7.HKVolumeProductZeros
public import Integration7.HKVolumeRightDistributivity
public import Integration7.HKWeightedZeroBlowupCongruence
public import Integration7.HKWeightedZeroDistributivity
public import Integration7.HKZeroAdditiveIntegration

@[expose] public section
set_option pp.universes true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.notation true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true



#check @IntegrationInACVF.Section7.HK.volume_iso_semiring_class_iso
#print axioms IntegrationInACVF.Section7.HK.volume_iso_semiring_class_iso
#check @IntegrationInACVF.Section7.HK.volume_iso_semiring_class_coprod
#print axioms IntegrationInACVF.Section7.HK.volume_iso_semiring_class_coprod
#check @IntegrationInACVF.Section7.HK.elementary_degree_one_semiring_factorization
#print axioms IntegrationInACVF.Section7.HK.elementary_degree_one_semiring_factorization
#check @IntegrationInACVF.Section7.HK.elementary_image_eq_of_basic
#print axioms IntegrationInACVF.Section7.HK.elementary_image_eq_of_basic
#check @IntegrationInACVF.Section7.HK.blowup_image_eq_of_basic
#print axioms IntegrationInACVF.Section7.HK.blowup_image_eq_of_basic
#check @IntegrationInACVF.Section7.HK.iterated_image_eq_of_basic
#print axioms IntegrationInACVF.Section7.HK.iterated_image_eq_of_basic
#check @IntegrationInACVF.Section7.HK.common_blowup_image_eq_of_basic
#print axioms IntegrationInACVF.Section7.HK.common_blowup_image_eq_of_basic
#check @IntegrationInACVF.Section7.HK.volumeBlowupUniversalComponent
#print axioms IntegrationInACVF.Section7.HK.volumeBlowupUniversalComponent
#check @IntegrationInACVF.Section7.HK.volumeBlowupUniversalDescend
#print axioms IntegrationInACVF.Section7.HK.volumeBlowupUniversalDescend
#check @IntegrationInACVF.Section7.HK.volume_blowup_universal_descend_class
#print axioms IntegrationInACVF.Section7.HK.volume_blowup_universal_descend_class
#check @IntegrationInACVF.Section7.HK.volume_blowup_universal_descend_projection
#print axioms IntegrationInACVF.Section7.HK.volume_blowup_universal_descend_projection
#check @IntegrationInACVF.Section7.HK.volume_blowup_universal_descend_unique
#print axioms IntegrationInACVF.Section7.HK.volume_blowup_universal_descend_unique
#check @IntegrationInACVF.Section7.HK.rvVolumeGradedBlowupProjection
#print axioms IntegrationInACVF.Section7.HK.rvVolumeGradedBlowupProjection
#check @IntegrationInACVF.Section7.HK.rvVolumeGradedBlowupProjection_of
#print axioms IntegrationInACVF.Section7.HK.rvVolumeGradedBlowupProjection_of
#check @IntegrationInACVF.Section7.HK.rvVolumeGradedBlowupProjection_surjective
#print axioms IntegrationInACVF.Section7.HK.rvVolumeGradedBlowupProjection_surjective
#check @IntegrationInACVF.Section7.HK.volumeIsoSemiringClass
#print axioms IntegrationInACVF.Section7.HK.volumeIsoSemiringClass
#check @IntegrationInACVF.Section7.HK.volume_iso_semiring_class_positive_product
#print axioms IntegrationInACVF.Section7.HK.volume_iso_semiring_class_positive_product
#check @IntegrationInACVF.Section7.HK.elementary_positive_semiring_factorization
#print axioms IntegrationInACVF.Section7.HK.elementary_positive_semiring_factorization
#check @IntegrationInACVF.Section7.HK.elementary_positive_image_eq_of_basic
#print axioms IntegrationInACVF.Section7.HK.elementary_positive_image_eq_of_basic
#check @IntegrationInACVF.Section7.HK.basic_volume_relation_projection
#print axioms IntegrationInACVF.Section7.HK.basic_volume_relation_projection
#check @IntegrationInACVF.Section7.HK.rawVolumeObjectClass
#print axioms IntegrationInACVF.Section7.HK.rawVolumeObjectClass
#check @IntegrationInACVF.Section7.HK.rawBasicVolumeDifference
#print axioms IntegrationInACVF.Section7.HK.rawBasicVolumeDifference
#check @IntegrationInACVF.Section7.HK.basicVolumeRelationIdeal
#print axioms IntegrationInACVF.Section7.HK.basicVolumeRelationIdeal
#check @IntegrationInACVF.Section7.HK.basicVolumeRelationIdealTwoSided
#print axioms IntegrationInACVF.Section7.HK.basicVolumeRelationIdealTwoSided
#check @IntegrationInACVF.Section7.HK.raw_basic_volume_difference_mem_kernel
#print axioms IntegrationInACVF.Section7.HK.raw_basic_volume_difference_mem_kernel
#check @IntegrationInACVF.Section7.HK.raw_volume_kernel_principal
#print axioms IntegrationInACVF.Section7.HK.raw_volume_kernel_principal
#check @IntegrationInACVF.Section7.HK.principalVolumeKernelQuotientEquiv
#print axioms IntegrationInACVF.Section7.HK.principalVolumeKernelQuotientEquiv
#check @IntegrationInACVF.Section7.HK.RawRVVolumeRing
#print axioms IntegrationInACVF.Section7.HK.RawRVVolumeRing
#check @IntegrationInACVF.Section7.HK.RVVolumeBlowupRing
#print axioms IntegrationInACVF.Section7.HK.RVVolumeBlowupRing
#check @IntegrationInACVF.Section7.HK.rawVolumeBlowupRingProjection
#print axioms IntegrationInACVF.Section7.HK.rawVolumeBlowupRingProjection
#check @IntegrationInACVF.Section7.HK.raw_volume_blowup_ring_projection_surjective
#print axioms IntegrationInACVF.Section7.HK.raw_volume_blowup_ring_projection_surjective
#check @IntegrationInACVF.Section7.HK.rawVolumeKernelIdeal
#print axioms IntegrationInACVF.Section7.HK.rawVolumeKernelIdeal
#check @IntegrationInACVF.Section7.HK.rawVolumeKernelIdealTwoSided
#print axioms IntegrationInACVF.Section7.HK.rawVolumeKernelIdealTwoSided
#check @IntegrationInACVF.Section7.HK.rawVolumeKernelIdealQuotientEquiv
#print axioms IntegrationInACVF.Section7.HK.rawVolumeKernelIdealQuotientEquiv
#check @IntegrationInACVF.Section7.HK.raw_volume_kernel_quotient_generator
#print axioms IntegrationInACVF.Section7.HK.raw_volume_kernel_quotient_generator
#check @IntegrationInACVF.Section7.HK.formToUpstream
#print axioms IntegrationInACVF.Section7.HK.formToUpstream
#check @IntegrationInACVF.Section7.HK.formFromUpstream
#print axioms IntegrationInACVF.Section7.HK.formFromUpstream
#check @IntegrationInACVF.Section7.HK.upstreamFormEquiv
#print axioms IntegrationInACVF.Section7.HK.upstreamFormEquiv
#check @IntegrationInACVF.Section7.HK.formToUpstream_weight
#print axioms IntegrationInACVF.Section7.HK.formToUpstream_weight
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.toUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.toUpstream
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.fromUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.fromUpstream
#check @IntegrationInACVF.Section7.HK.upstreamRVZeroEquiv
#print axioms IntegrationInACVF.Section7.HK.upstreamRVZeroEquiv
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.toUpstream_weight
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.toUpstream_weight
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.toUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.toUpstream
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.fromUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.fromUpstream
#check @IntegrationInACVF.Section7.HK.upstream_zero_iso_iff
#print axioms IntegrationInACVF.Section7.HK.upstream_zero_iso_iff
#check @IntegrationInACVF.Section7.HK.zero_dimension_auxiliary_iff
#print axioms IntegrationInACVF.Section7.HK.zero_dimension_auxiliary_iff
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.toUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.toUpstream
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.fromUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.fromUpstream
#check @IntegrationInACVF.Section7.HK.upstreamVFZeroEquiv
#print axioms IntegrationInACVF.Section7.HK.upstreamVFZeroEquiv
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.toUpstream_weight
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.toUpstream_weight
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.toUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.toUpstream
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.fromUpstream
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.fromUpstream
#check @IntegrationInACVF.Section7.HK.upstream_zero_vf_iso_iff
#print axioms IntegrationInACVF.Section7.HK.upstream_zero_vf_iso_iff
#check @IntegrationInACVF.Section7.HK.upstream_zero_lift
#print axioms IntegrationInACVF.Section7.HK.upstream_zero_lift
#check @IntegrationInACVF.Section7.HK.MuIsp
#print axioms IntegrationInACVF.Section7.HK.MuIsp
#check @IntegrationInACVF.Section7.HK.muIsp_refl
#print axioms IntegrationInACVF.Section7.HK.muIsp_refl
#check @IntegrationInACVF.Section7.HK.muIsp_symm
#print axioms IntegrationInACVF.Section7.HK.muIsp_symm
#check @IntegrationInACVF.Section7.HK.muIsp_trans
#print axioms IntegrationInACVF.Section7.HK.muIsp_trans
#check @IntegrationInACVF.Section7.HK.muIspSetoid
#print axioms IntegrationInACVF.Section7.HK.muIspSetoid
#check @IntegrationInACVF.Section7.HK.muIsp_coprod
#print axioms IntegrationInACVF.Section7.HK.muIsp_coprod
#check @IntegrationInACVF.Section7.HK.muIsp_product
#print axioms IntegrationInACVF.Section7.HK.muIsp_product
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGMul
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGMul
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGOne
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGOne
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGMonoid
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGMonoid
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGNonUnitalNonAssocSemiring
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGNonUnitalNonAssocSemiring
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGSemiring
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesGSemiring
#check @IntegrationInACVF.Section7.HK.RVVolumeBlowupSemiring
#print axioms IntegrationInACVF.Section7.HK.RVVolumeBlowupSemiring
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesZeroAddCommMonoid
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesZeroAddCommMonoid
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesZeroAddCommMonoid
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesZeroAddCommMonoid
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClass_heq_of_iso
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClass_heq_of_iso
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClass_heq_of_iso
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClass_heq_of_iso
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClass_product
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClass_product
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClass_product
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClass_product
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoSetoid
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoSetoid
#check @IntegrationInACVF.Section7.HK.RVVolumeIsoClasses
#print axioms IntegrationInACVF.Section7.HK.RVVolumeIsoClasses
#check @IntegrationInACVF.Section7.HK.RVBlowupClasses
#print axioms IntegrationInACVF.Section7.HK.RVBlowupClasses
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClass
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClass
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClass
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClass
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClass_eq_iff
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClass_eq_iff
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClass_eq_iff
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClass_eq_iff
#check @IntegrationInACVF.Section7.HK.muIsp_of_iso
#print axioms IntegrationInACVF.Section7.HK.muIsp_of_iso
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesAdd
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesAdd
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesZero
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesZero
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesAddCommMonoid
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesAddCommMonoid
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesAdd
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesAdd
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesZero
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesZero
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesAddCommMonoid
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesAddCommMonoid
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesProduct
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesProduct
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesProduct
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupClassesProduct
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupProjection
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupProjection
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupProjection_surjective
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupProjection_surjective
#check @IntegrationInACVF.Section7.HK.rvVolumeBlowupProjection_product
#print axioms IntegrationInACVF.Section7.HK.rvVolumeBlowupProjection_product
#check @IntegrationInACVF.Section7.HK.zeroCoprodIso
#print axioms IntegrationInACVF.Section7.HK.zeroCoprodIso
#check @IntegrationInACVF.Section7.HK.zeroCoprodSwap
#print axioms IntegrationInACVF.Section7.HK.zeroCoprodSwap
#check @IntegrationInACVF.Section7.HK.zeroCoprodAssoc
#print axioms IntegrationInACVF.Section7.HK.zeroCoprodAssoc
#check @IntegrationInACVF.Section7.HK.zeroCoprodEmptyEmbedding
#print axioms IntegrationInACVF.Section7.HK.zeroCoprodEmptyEmbedding
#check @IntegrationInACVF.Section7.HK.coprodIso
#print axioms IntegrationInACVF.Section7.HK.coprodIso
#check @IntegrationInACVF.Section7.HK.coprodAssocIso
#print axioms IntegrationInACVF.Section7.HK.coprodAssocIso
#check @IntegrationInACVF.Section7.HK.coprodSwapIso
#print axioms IntegrationInACVF.Section7.HK.coprodSwapIso
#check @IntegrationInACVF.Section7.HK.coprodRightUnitIso
#print axioms IntegrationInACVF.Section7.HK.coprodRightUnitIso
#check @IntegrationInACVF.Section7.HK.coprodLeftUnitIso
#print axioms IntegrationInACVF.Section7.HK.coprodLeftUnitIso
#check @IntegrationInACVF.Section7.HK.coprod
#print axioms IntegrationInACVF.Section7.HK.coprod
#check @IntegrationInACVF.Section7.HK.empty
#print axioms IntegrationInACVF.Section7.HK.empty
#check @IntegrationInACVF.Section7.HK.unit
#print axioms IntegrationInACVF.Section7.HK.unit
#check @IntegrationInACVF.Section7.HK.data_coprod_ofData
#print axioms IntegrationInACVF.Section7.HK.data_coprod_ofData
#check @IntegrationInACVF.Section7.HK.coprod_underlying
#print axioms IntegrationInACVF.Section7.HK.coprod_underlying
#check @IntegrationInACVF.Section7.HK.coprod_density_left
#print axioms IntegrationInACVF.Section7.HK.coprod_density_left
#check @IntegrationInACVF.Section7.HK.coprod_density_right
#print axioms IntegrationInACVF.Section7.HK.coprod_density_right
#check @IntegrationInACVF.Section7.HK.zero_coprod_cases
#print axioms IntegrationInACVF.Section7.HK.zero_coprod_cases
#check @IntegrationInACVF.Section7.HK.dataOfObject
#print axioms IntegrationInACVF.Section7.HK.dataOfObject
#check @IntegrationInACVF.Section7.HK.dataOfObject_ofData
#print axioms IntegrationInACVF.Section7.HK.dataOfObject_ofData
#check @IntegrationInACVF.Section7.HK.dataRelabelIso
#print axioms IntegrationInACVF.Section7.HK.dataRelabelIso
#check @IntegrationInACVF.Section7.HK.dataReindexedIso
#print axioms IntegrationInACVF.Section7.HK.dataReindexedIso
#check @IntegrationInACVF.Section7.HK.productData
#print axioms IntegrationInACVF.Section7.HK.productData
#check @IntegrationInACVF.Section7.HK.productData_ofData
#print axioms IntegrationInACVF.Section7.HK.productData_ofData
#check @IntegrationInACVF.Section7.HK.productData_density_pair
#print axioms IntegrationInACVF.Section7.HK.productData_density_pair
#check @IntegrationInACVF.Section7.HK.product_density_pair
#print axioms IntegrationInACVF.Section7.HK.product_density_pair
#check @IntegrationInACVF.Section7.HK.isoRefl
#print axioms IntegrationInACVF.Section7.HK.isoRefl
#check @IntegrationInACVF.Section7.HK.isoSymm
#print axioms IntegrationInACVF.Section7.HK.isoSymm
#check @IntegrationInACVF.Section7.HK.isoTrans
#print axioms IntegrationInACVF.Section7.HK.isoTrans
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGMul
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGMul
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGOne
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGOne
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGMonoid
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGMonoid
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGNonUnitalNonAssocSemiring
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGNonUnitalNonAssocSemiring
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGSemiring
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoClassesGSemiring
#check @IntegrationInACVF.Section7.HK.RVVolumeIsoSemiring
#print axioms IntegrationInACVF.Section7.HK.RVVolumeIsoSemiring
#check @IntegrationInACVF.Section7.HK.leftProductCoprodFoldIso
#print axioms IntegrationInACVF.Section7.HK.leftProductCoprodFoldIso
#check @IntegrationInACVF.Section7.HK.productLeftDistribIso
#print axioms IntegrationInACVF.Section7.HK.productLeftDistribIso
#check @IntegrationInACVF.Section7.HK.productAssocIso
#print axioms IntegrationInACVF.Section7.HK.productAssocIso
#check @IntegrationInACVF.Section7.HK.productRightUnitIso
#print axioms IntegrationInACVF.Section7.HK.productRightUnitIso
#check @IntegrationInACVF.Section7.HK.productLeftUnitIso
#print axioms IntegrationInACVF.Section7.HK.productLeftUnitIso
#check @IntegrationInACVF.Section7.HK.empty_domain
#print axioms IntegrationInACVF.Section7.HK.empty_domain
#check @IntegrationInACVF.Section7.HK.productRightZeroIso
#print axioms IntegrationInACVF.Section7.HK.productRightZeroIso
#check @IntegrationInACVF.Section7.HK.productLeftZeroIso
#print axioms IntegrationInACVF.Section7.HK.productLeftZeroIso
#check @IntegrationInACVF.Section7.HK.productCoprodFoldIso
#print axioms IntegrationInACVF.Section7.HK.productCoprodFoldIso
#check @IntegrationInACVF.Section7.HK.productRightDistribIso
#print axioms IntegrationInACVF.Section7.HK.productRightDistribIso
#check @IntegrationInACVF.Section7.HK.weightedZeroBlowup
#print axioms IntegrationInACVF.Section7.HK.weightedZeroBlowup
#check @IntegrationInACVF.Section7.HK.weightedZeroIterated
#print axioms IntegrationInACVF.Section7.HK.weightedZeroIterated
#check @IntegrationInACVF.Section7.HK.weightedZeroEquivalent
#print axioms IntegrationInACVF.Section7.HK.weightedZeroEquivalent
#check @IntegrationInACVF.Section7.HK.weightedPositiveZeroEquivalent
#print axioms IntegrationInACVF.Section7.HK.weightedPositiveZeroEquivalent
#check @IntegrationInACVF.Section7.HK.weightedZeroProdEquivalent
#print axioms IntegrationInACVF.Section7.HK.weightedZeroProdEquivalent
#check @IntegrationInACVF.Section7.HK.weightedProdZeroEquivalent
#print axioms IntegrationInACVF.Section7.HK.weightedProdZeroEquivalent
#check @IntegrationInACVF.Section7.HK.volumeZeroProductCoprodFold_coordinates
#print axioms IntegrationInACVF.Section7.HK.volumeZeroProductCoprodFold_coordinates
#check @IntegrationInACVF.Section7.HK.volumeZeroProductCoprodFold_density
#print axioms IntegrationInACVF.Section7.HK.volumeZeroProductCoprodFold_density
#check @IntegrationInACVF.Section7.HK.volumeZeroProductRightDistribIso
#print axioms IntegrationInACVF.Section7.HK.volumeZeroProductRightDistribIso
#check @IntegrationInACVF.Section7.HK.zeroVFAddCommMonoid
#print axioms IntegrationInACVF.Section7.HK.zeroVFAddCommMonoid
#check @IntegrationInACVF.Section7.HK.zeroAdditiveIntegrationEquiv
#print axioms IntegrationInACVF.Section7.HK.zeroAdditiveIntegrationEquiv
