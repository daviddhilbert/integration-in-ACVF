module

public import Integration7.HKZeroVFVolumeObjects
public import Integration7.HKZeroVolumeDescent
public import Integration7.HKZeroVolumeIntegration
public import Integration7.HKZeroVolumeLiftSurjectivity
public import Integration7.HKZeroVolumeLifts

@[expose] public section
set_option pp.universes true
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.notation true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true



#check @IntegrationInACVF.Section7.HK.finiteZeroVFMap
#print axioms IntegrationInACVF.Section7.HK.finiteZeroVFMap
#check @IntegrationInACVF.Section7.HK.finiteZeroVFMap_symm_apply
#print axioms IntegrationInACVF.Section7.HK.finiteZeroVFMap_symm_apply
#check @IntegrationInACVF.Section7.HK.finiteZeroVFMap_apply_symm
#print axioms IntegrationInACVF.Section7.HK.finiteZeroVFMap_apply_symm
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeObject
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeObject
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.mk
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeObject.mk
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeIso
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeIso
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.mk
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.mk
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.refl
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.refl
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.trans
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.trans
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.symm
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeIso.symm
#check @IntegrationInACVF.Section7.HK.zeroVFVolumeSetoid
#print axioms IntegrationInACVF.Section7.HK.zeroVFVolumeSetoid
#check @IntegrationInACVF.Section7.HK.ZeroVFVolumeClasses
#print axioms IntegrationInACVF.Section7.HK.ZeroVFVolumeClasses
#check @IntegrationInACVF.Section7.HK.zeroVolumeDescentOfDensity
#print axioms IntegrationInACVF.Section7.HK.zeroVolumeDescentOfDensity
#check @IntegrationInACVF.Section7.HK.corollary_2_34_zero_weighted
#print axioms IntegrationInACVF.Section7.HK.corollary_2_34_zero_weighted
#check @IntegrationInACVF.Section7.HK.corollary_2_34_zero_weighted_underlying
#print axioms IntegrationInACVF.Section7.HK.corollary_2_34_zero_weighted_underlying
#check @IntegrationInACVF.Section7.HK.zeroLiftOnClasses
#print axioms IntegrationInACVF.Section7.HK.zeroLiftOnClasses
#check @IntegrationInACVF.Section7.HK.zeroLiftOnClasses_bijective
#print axioms IntegrationInACVF.Section7.HK.zeroLiftOnClasses_bijective
#check @IntegrationInACVF.Section7.HK.zeroVolumeIntegrationEquiv
#print axioms IntegrationInACVF.Section7.HK.zeroVolumeIntegrationEquiv
#check @IntegrationInACVF.Section7.HK.zero_integration_lift
#print axioms IntegrationInACVF.Section7.HK.zero_integration_lift
#check @IntegrationInACVF.Section7.HK.VFVolumeObject
#print axioms IntegrationInACVF.Section7.HK.VFVolumeObject
#check @IntegrationInACVF.Section7.HK.volumeLift
#print axioms IntegrationInACVF.Section7.HK.volumeLift
#check @IntegrationInACVF.Section7.HK.VFVolumeClasses
#print axioms IntegrationInACVF.Section7.HK.VFVolumeClasses
#check @IntegrationInACVF.Section7.HK.RVVolumeBlowupClasses
#print axioms IntegrationInACVF.Section7.HK.RVVolumeBlowupClasses
#check @IntegrationInACVF.Section7.HK.vfClass
#print axioms IntegrationInACVF.Section7.HK.vfClass
#check @IntegrationInACVF.Section7.HK.rvClass
#print axioms IntegrationInACVF.Section7.HK.rvClass
#check @IntegrationInACVF.Section7.HK.volumeIntegrationEquiv
#print axioms IntegrationInACVF.Section7.HK.volumeIntegrationEquiv
#check @IntegrationInACVF.Section7.HK.volume_integration_lift
#print axioms IntegrationInACVF.Section7.HK.volume_integration_lift
#check @IntegrationInACVF.Section7.HK.zero_volume_lift_presentation_exists
#print axioms IntegrationInACVF.Section7.HK.zero_volume_lift_presentation_exists
#check @IntegrationInACVF.Section7.HK.zeroLift
#print axioms IntegrationInACVF.Section7.HK.zeroLift
#check @IntegrationInACVF.Section7.HK.zeroLift_density
#print axioms IntegrationInACVF.Section7.HK.zeroLift_density
#check @IntegrationInACVF.Section7.HK.zeroLiftIso
#print axioms IntegrationInACVF.Section7.HK.zeroLiftIso
#check @IntegrationInACVF.Section7.HK.zeroRVOfLiftIso
#print axioms IntegrationInACVF.Section7.HK.zeroRVOfLiftIso
#check @IntegrationInACVF.Section7.HK.zero_lift_iso_iff
#print axioms IntegrationInACVF.Section7.HK.zero_lift_iso_iff
