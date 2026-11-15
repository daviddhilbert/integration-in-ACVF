import Integration7.SupportedUnivVolumeEquivalences
import Integration7.SemimoduleScalarExtensionEquivalences
import Integration7.NormalizedSupportedVolumeFunctions

/-! The normalized supported module on the full VF domain is exactly
the existing normalized function module, including ordinary RV[0]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ)

def normalizedSupportedUnivEquiv :
    NormalizedSupportedVolumeFunction hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      ≃ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  (scalarExtensionLinearEquiv (normalizedVolumeCoefficientMap hc C) (supportedUnivPositiveGradedEquiv hc C n)).trans
    (normalizedPositiveDegreeVolumeEquiv hc C n)

theorem normalized_supported_univ_equiv_toLinearMap :
    (normalizedSupportedUnivEquiv hc C n).toLinearMap =
      normalizedSupportedVolumeForget hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) := by
  apply scalar_extension_linearMap_ext (normalizedVolumeCoefficientMap hc C)
  intro g
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C)
      (gradedShiftLinearEmbedding (aeVolumeFunctionGradedAction hc C n) 1)
      (scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedUnivPositiveGradedMap hc C n)
        (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ g)) =
    scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedForget hc C (DefSet.univ _ _))
      (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ g)
  rw [scalar_extension_map_generator,scalar_extension_map_generator,scalar_extension_map_generator]
  rfl

theorem normalized_supported_univ_equiv_forget
    (f : NormalizedSupportedVolumeFunction hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))) :
    normalizedSupportedUnivEquiv hc C n f = normalizedSupportedVolumeForget hc C (DefSet.univ _ _) f :=
  congrArg (fun I => I f) (normalized_supported_univ_equiv_toLinearMap hc C n)

theorem normalized_supported_univ_inverse_positive (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    (normalizedSupportedUnivEquiv hc C n).symm (normalizedPositiveVolumeFunction hc C n j f) =
      normalizedSupportedVolumeGenerator hc C (DefSet.univ _ _)
        (DirectSum.of (SupportedAERVVolumeFunction hc C (DefSet.univ _ _)) j (supportedVolumeUnivLift hc C n j f)) := by
  apply (normalizedSupportedUnivEquiv hc C n).injective
  rw [LinearEquiv.apply_symm_apply,normalized_supported_univ_equiv_forget,
    normalized_supported_volume_forget_generator,supported_volume_univ_forget_lift]
end IntegrationInACVF.Section7
