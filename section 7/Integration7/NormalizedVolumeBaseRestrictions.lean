import Integration7.SupportedPositiveGradedRestrictions
import Integration7.NormalizedSupportedVolumeFunctions

/-! Restriction to an arbitrary definable VF subset is a genuine
normalized linear map. It splits the actual supported-module inclusion,
so that inclusion remains injective after scalar extension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedVolumeRestriction
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedSupportedVolumeFunction hc C X :=
  (scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (positiveGradedVolumeRestriction hc C X)).comp
    (normalizedPositiveDegreeVolumeEquiv hc C n).symm.toLinearMap

theorem normalized_supported_volume_forget_factorization
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    normalizedSupportedVolumeForget hc C X = (normalizedPositiveDegreeVolumeEquiv hc C n).toLinearMap.comp
      (scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedForgetShift hc C X)) := by
  apply scalar_extension_linearMap_ext (normalizedVolumeCoefficientMap hc C)
  intro g
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedForget hc C X)
      (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ g) =
    normalizedPositiveDegreeVolumeEquiv hc C n
      (scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedForgetShift hc C X)
        (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ g))
  rw [scalar_extension_map_generator,scalar_extension_map_generator,normalized_positive_degree_equiv_generator]
  rfl

theorem normalized_volume_restriction_forget
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    (normalizedVolumeRestriction hc C X).comp (normalizedSupportedVolumeForget hc C X) = LinearMap.id := by
  have hComp := congrArg (scalarExtensionMap (normalizedVolumeCoefficientMap hc C))
    (positive_graded_volume_restriction_forget hc C X)
  rw [scalar_extension_map_comp,scalar_extension_map_id] at hComp
  apply LinearMap.ext
  intro f
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (positiveGradedVolumeRestriction hc C X)
    ((normalizedPositiveDegreeVolumeEquiv hc C n).symm (normalizedSupportedVolumeForget hc C X f)) = f
  have hF := congrArg (fun I => I f) (normalized_supported_volume_forget_factorization hc C X)
  change normalizedSupportedVolumeForget hc C X f = normalizedPositiveDegreeVolumeEquiv hc C n
    (scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedForgetShift hc C X) f) at hF
  rw [hF,LinearEquiv.symm_apply_apply]
  exact congrArg (fun I => I f) hComp

theorem normalized_supported_volume_forget_injective
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Function.Injective (normalizedSupportedVolumeForget hc C X) := by
  intro f g h
  have hs := normalized_volume_restriction_forget hc C X
  exact (congrArg (fun I => I f) hs).symm.trans
    ((congrArg (normalizedVolumeRestriction hc C X) h).trans (congrArg (fun I => I g) hs))

theorem normalized_positive_degree_inverse_positive (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    (normalizedPositiveDegreeVolumeEquiv hc C n).symm (normalizedPositiveVolumeFunction hc C n j f) =
      scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _
        (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) j f) := by
  apply (normalizedPositiveDegreeVolumeEquiv hc C n).injective
  rw [LinearEquiv.apply_symm_apply,normalized_positive_degree_equiv_generator]
  exact congrArg (normalizedVolumeFunctionGenerator hc C n)
    (graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 j f).symm

theorem normalized_volume_restriction_positive (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    normalizedVolumeRestriction hc C X (normalizedPositiveVolumeFunction hc C n j f) =
      normalizedSupportedVolumeGenerator hc C X
        (DirectSum.of (SupportedAERVVolumeFunction hc C X) j (aeVolumeFunctionRestrictToSupported hc C X f)) := by
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (positiveGradedVolumeRestriction hc C X)
    ((normalizedPositiveDegreeVolumeEquiv hc C n).symm (normalizedPositiveVolumeFunction hc C n j f)) = _
  rw [normalized_positive_degree_inverse_positive,scalar_extension_map_generator,positive_graded_volume_restriction_of]
  rfl
end IntegrationInACVF.Section7
