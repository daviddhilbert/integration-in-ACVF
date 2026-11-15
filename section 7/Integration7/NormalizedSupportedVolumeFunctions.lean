import Integration7.SupportedPositiveGradedForget
import Integration7.SupportedPositiveGradedJacobians
import Integration7.SemimoduleScalarExtensionMaps
import Integration7.NormalizedPositiveJacobianIntegrals

/-! The actual positive supported graded module has a balanced
normalized scalar extension. Its Jacobian map is genuinely linear over
the normalized coefficient ring, and retains the geometric generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev NormalizedSupportedVolumeFunction
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  SemimoduleScalarExtension (normalizedVolumeCoefficientMap hc C) (SupportedPositiveGradedVolumeFunction hc C X)

def normalizedSupportedVolumeGenerator
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedPositiveGradedVolumeFunction hc C X →+ NormalizedSupportedVolumeFunction hc C X :=
  scalarExtensionGeneratorHom (normalizedVolumeCoefficientMap hc C) _

def normalizedSupportedVolumeForget
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedForget hc C X)

def normalizedSupportedVolumeJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedSupportedVolumeFunction hc C Y :=
  scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedJacobian hc C φ hφ)

theorem normalized_supported_volume_forget_generator
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : SupportedAERVVolumeFunction hc C X j) :
    normalizedSupportedVolumeForget hc C X
      (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f)) =
      normalizedPositiveVolumeFunction hc C n j (supportedVolumeFunctionForget hc C X f) := by
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedForget hc C X)
    (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _
      (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f)) = _
  rw [scalar_extension_map_generator,supported_positive_graded_forget_of]
  rfl

theorem normalized_supported_volume_jacobian_generator
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (j : ℕ)
    (f : SupportedAERVVolumeFunction hc C X j) :
    normalizedSupportedVolumeJacobian hc C φ hφ
      (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f)) =
      normalizedSupportedVolumeGenerator hc C Y (DirectSum.of (SupportedAERVVolumeFunction hc C Y) j
        (supportedVolumeFunctionJacobian hc C φ hφ f)) := by
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C) (supportedPositiveGradedJacobian hc C φ hφ)
    (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _
      (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f)) = _
  rw [scalar_extension_map_generator,supported_positive_graded_jacobian_of]
  rfl
end IntegrationInACVF.Section7
