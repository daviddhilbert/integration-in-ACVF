module

public import Integration7.HKCorrectionLibrary
public import Integration7.HKDegreeOnePrincipalFactors
public import Integration7.HKDegreeOneVolumeFactors
public import Integration7.HKMixedVolumeIsomorphisms
public import Integration7.HKRVProductBridges
public import Integration7.HKRVProductIsomorphisms
public import Integration7.HKRVVolumeObjects
public import Integration7.HKRVVolumeProducts
public import Integration7.HKVolumeFormTransport
public import Integration7.HKWeightedZeroBlowups
public import Integration7.HKZeroFamilyChangeOfVariables
public import Integration7.HKZeroRVVolumeIsomorphisms
public import Integration7.HKZeroVolumeFamilies

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section
set_option pp.universes true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.notation true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true



#check @IntegrationInACVF.Section7.HK.degreeOneHeadConeVolumeIso
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadConeVolumeIso
#check @IntegrationInACVF.Section7.HK.elementary_degree_one_weighted_factorization
#print axioms IntegrationInACVF.Section7.HK.elementary_degree_one_weighted_factorization
#check @IntegrationInACVF.Section7.HK.elementary_degree_one_product_factorization
#print axioms IntegrationInACVF.Section7.HK.elementary_degree_one_product_factorization
#check @IntegrationInACVF.Section7.HK.degreeOneHeadFactor
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadFactor
#check @IntegrationInACVF.Section7.HK.degreeOneHeadFactor_density
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadFactor_density
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointPair
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointPair
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointPair_bijective
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointPair_bijective
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointMap
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointMap
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_bijective
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_bijective
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_unpack
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_unpack
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_coordinates
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_coordinates
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_density
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_density
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_essential
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointMap_essential
#check @IntegrationInACVF.Section7.HK.degreeOneHeadPointVolumeIso
#print axioms IntegrationInACVF.Section7.HK.degreeOneHeadPointVolumeIso
#check @IntegrationInACVF.Section7.HK.positiveZeroProductIso
#print axioms IntegrationInACVF.Section7.HK.positiveZeroProductIso
#check @IntegrationInACVF.Section7.HK.mixedProductSwapIso
#print axioms IntegrationInACVF.Section7.HK.mixedProductSwapIso
#check @IntegrationInACVF.Section7.HK.zeroProductIso
#print axioms IntegrationInACVF.Section7.HK.zeroProductIso
#check @IntegrationInACVF.Section7.HK.productPositiveZeroIso
#print axioms IntegrationInACVF.Section7.HK.productPositiveZeroIso
#check @IntegrationInACVF.Section7.HK.productZeroPositiveIso
#print axioms IntegrationInACVF.Section7.HK.productZeroPositiveIso
#check @IntegrationInACVF.Section7.HK.zeroZeroProductIso
#print axioms IntegrationInACVF.Section7.HK.zeroZeroProductIso
#check @IntegrationInACVF.Section7.HK.productIso
#print axioms IntegrationInACVF.Section7.HK.productIso
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.mk
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.mk
#check @IntegrationInACVF.Section7.HK.RVVolumeObject
#print axioms IntegrationInACVF.Section7.HK.RVVolumeObject
#check @IntegrationInACVF.Section7.HK.underlying
#print axioms IntegrationInACVF.Section7.HK.underlying
#check @IntegrationInACVF.Section7.HK.form
#print axioms IntegrationInACVF.Section7.HK.form
#check @IntegrationInACVF.Section7.HK.ofForm
#print axioms IntegrationInACVF.Section7.HK.ofForm
#check @IntegrationInACVF.Section7.HK.ofForm_underlying
#print axioms IntegrationInACVF.Section7.HK.ofForm_underlying
#check @IntegrationInACVF.Section7.HK.ofForm_density
#print axioms IntegrationInACVF.Section7.HK.ofForm_density
#check @IntegrationInACVF.Section7.HK.ofData
#print axioms IntegrationInACVF.Section7.HK.ofData
#check @IntegrationInACVF.Section7.HK.ofData_underlying
#print axioms IntegrationInACVF.Section7.HK.ofData_underlying
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.unitForm
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.unitForm
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.unitForm_density
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.unitForm_density
#check @IntegrationInACVF.Section7.HK.product
#print axioms IntegrationInACVF.Section7.HK.product
#check @IntegrationInACVF.Section7.HK.product_underlying
#print axioms IntegrationInACVF.Section7.HK.product_underlying
#check @IntegrationInACVF.Section7.HK.product_density
#print axioms IntegrationInACVF.Section7.HK.product_density
#check @IntegrationInACVF.Section7.HK.zeroProductMultiplier
#print axioms IntegrationInACVF.Section7.HK.zeroProductMultiplier
#check @IntegrationInACVF.Section7.HK.zeroProduct
#print axioms IntegrationInACVF.Section7.HK.zeroProduct
#check @IntegrationInACVF.Section7.HK.zeroProduct_density
#print axioms IntegrationInACVF.Section7.HK.zeroProduct_density
#check @IntegrationInACVF.Section7.HK.zeroProduct_coordinates
#print axioms IntegrationInACVF.Section7.HK.zeroProduct_coordinates
#check @IntegrationInACVF.Section7.HK.positiveZeroMultiplier
#print axioms IntegrationInACVF.Section7.HK.positiveZeroMultiplier
#check @IntegrationInACVF.Section7.HK.positiveZeroProduct
#print axioms IntegrationInACVF.Section7.HK.positiveZeroProduct
#check @IntegrationInACVF.Section7.HK.positiveZeroProduct_density
#print axioms IntegrationInACVF.Section7.HK.positiveZeroProduct_density
#check @IntegrationInACVF.Section7.HK.positiveZeroProduct_coordinates
#print axioms IntegrationInACVF.Section7.HK.positiveZeroProduct_coordinates
#check @IntegrationInACVF.Section7.HK.multiplyForm
#print axioms IntegrationInACVF.Section7.HK.multiplyForm
#check @IntegrationInACVF.Section7.HK.multiplyForm_density
#print axioms IntegrationInACVF.Section7.HK.multiplyForm_density
#check @IntegrationInACVF.Section7.HK.multiplyForm_ratio
#print axioms IntegrationInACVF.Section7.HK.multiplyForm_ratio
#check @IntegrationInACVF.Section7.HK.multiplyFormIso
#print axioms IntegrationInACVF.Section7.HK.multiplyFormIso
#check @IntegrationInACVF.Section7.HK.weightedZeroElementary
#print axioms IntegrationInACVF.Section7.HK.weightedZeroElementary
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transport
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transport
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transport_density
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transport_density
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transportVolumeBijection
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transportVolumeBijection
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transport_volume_class
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.transport_volume_class
#check @IntegrationInACVF.Section7.HK.zero_family_change_of_variables_integral
#print axioms IntegrationInACVF.Section7.HK.zero_family_change_of_variables_integral
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.mk
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.mk
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.refl
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.refl
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.trans
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.trans
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.symm
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.symm
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.ofBijection
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.ofBijection
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.unitForm
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeIso.unitForm
#check @IntegrationInACVF.Section7.HK.zero_unit_form_iso_iff
#print axioms IntegrationInACVF.Section7.HK.zero_unit_form_iso_iff
#check @IntegrationInACVF.Section7.HK.rvVolumeIsoInDegree
#print axioms IntegrationInACVF.Section7.HK.rvVolumeIsoInDegree
#check @IntegrationInACVF.Section7.HK.zeroRVVolumeSetoid
#print axioms IntegrationInACVF.Section7.HK.zeroRVVolumeSetoid
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeClasses
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeClasses
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.extend
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.extend
#check @IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.extend_density
#print axioms IntegrationInACVF.Section7.HK.ZeroRVVolumeObject.extend_density
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.mk
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.mk
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.toOrdinary
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.toOrdinary
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.ofOrdinary
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.ofOrdinary
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.rowObject
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.rowObject
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.rowInContext
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.rowInContext
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.rowInContext_density
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.rowInContext_density
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.fullVFObject
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.fullVFObject
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.fullVFObject_density
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.fullVFObject_density
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.ofOrdinary_fullVFObject
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.ofOrdinary_fullVFObject
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.pointPad
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.pointPad
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.pointPad_row_density
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeFamily.pointPad_row_density
