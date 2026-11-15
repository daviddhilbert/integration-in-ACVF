import Integration7.NormalizedVolumeDomainJacobians
import Integration7.NormalizedVolumeSupportProjections
import Integration7.NormalizedPositiveFunctionGeneration

/-! The normalized domain Jacobian is determined on genuine positive
geometric generators and depends only on the actual source restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem normalized_volume_domain_jacobian_generator
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    normalizedVolumeDomainJacobian hc C φ hφ (normalizedPositiveVolumeFunction hc C n j f) =
      normalizedPositiveVolumeFunction hc C n j (supportedVolumeFunctionForget hc C Y
        (supportedVolumeFunctionJacobian hc C φ hφ (aeVolumeFunctionRestrictToSupported hc C X f))) := by
  change normalizedSupportedVolumeForget hc C Y (normalizedSupportedVolumeJacobian hc C φ hφ
    (normalizedVolumeRestriction hc C X (normalizedPositiveVolumeFunction hc C n j f))) = _
  rw [normalized_volume_restriction_positive,normalized_supported_volume_jacobian_generator,
    normalized_supported_volume_forget_generator]

theorem normalized_volume_domain_jacobian_unique
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (J : NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n)
    (hJ : ∀ j (f : AERVVolumeFunction hc C n j),
      J (normalizedPositiveVolumeFunction hc C n j f) = normalizedPositiveVolumeFunction hc C n j
        (supportedVolumeFunctionForget hc C Y
          (supportedVolumeFunctionJacobian hc C φ hφ (aeVolumeFunctionRestrictToSupported hc C X f)))) :
    J = normalizedVolumeDomainJacobian hc C φ hφ :=
  normalized_volume_function_linearMap_ext_positive hc C n (fun j f =>
    (hJ j f).trans (normalized_volume_domain_jacobian_generator hc C φ hφ j f).symm)

theorem normalized_volume_domain_jacobian_projection
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (f : NormalizedVolumeFunction hc C n) :
    normalizedVolumeDomainJacobian hc C φ hφ (normalizedVolumeSupportProjection hc C X f) =
      normalizedVolumeDomainJacobian hc C φ hφ f :=
  normalized_volume_domain_jacobian_forget hc C φ hφ (normalizedVolumeRestriction hc C X f)
end IntegrationInACVF.Section7
