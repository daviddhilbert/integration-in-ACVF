module

public import Integration7.NormalizedVolumeSupports
public import Integration7.NormalizedSupportedVolumeIntegrals

@[expose] public section

/-! Bijections between arbitrary definable VF subsets induce actual
linear Jacobian operators on the full normalized function space. On
functions supported in the source they preserve the total integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedVolumeDomainJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  (normalizedSupportedVolumeForget hc C Y).comp
    ((normalizedSupportedVolumeJacobian hc C φ hφ).comp (normalizedVolumeRestriction hc C X))

theorem normalized_volume_domain_jacobian_forget
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (f : NormalizedSupportedVolumeFunction hc C X) :
    normalizedVolumeDomainJacobian hc C φ hφ (normalizedSupportedVolumeForget hc C X f) =
      normalizedSupportedVolumeForget hc C Y (normalizedSupportedVolumeJacobian hc C φ hφ f) := by
  change normalizedSupportedVolumeForget hc C Y (normalizedSupportedVolumeJacobian hc C φ hφ
    (normalizedVolumeRestriction hc C X (normalizedSupportedVolumeForget hc C X f))) = _
  rw [show normalizedVolumeRestriction hc C X (normalizedSupportedVolumeForget hc C X f)=f from
    congrArg (fun I => I f) (normalized_volume_restriction_forget hc C X)]

theorem normalized_volume_domain_jacobian_has_support
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (f : NormalizedVolumeFunction hc C n) :
    HasNormalizedVolumeSupport hc C Y (normalizedVolumeDomainJacobian hc C φ hφ f) :=
  normalized_supported_volume_has_support hc C Y _

theorem normalized_volume_domain_jacobian_positive
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (j : ℕ) (f : SupportedAERVVolumeFunction hc C X j) :
    normalizedVolumeDomainJacobian hc C φ hφ
        (normalizedPositiveVolumeFunction hc C n j (supportedVolumeFunctionForget hc C X f)) =
      normalizedPositiveVolumeFunction hc C n j
        (supportedVolumeFunctionForget hc C Y (supportedVolumeFunctionJacobian hc C φ hφ f)) := by
  rw [← normalized_supported_volume_forget_generator hc C X j f,normalized_volume_domain_jacobian_forget,
    normalized_supported_volume_jacobian_generator,normalized_supported_volume_forget_generator]

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_volume_domain_change_of_variables
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (f : NormalizedVolumeFunction hc C n) (hf : HasNormalizedVolumeSupport hc C X f) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (normalizedVolumeDomainJacobian hc C φ hφ f) := by
  obtain ⟨g,rfl⟩ := hf
  rw [normalized_volume_domain_jacobian_forget]
  exact normalized_supported_volume_change_of_variables_value hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ g
end IntegrationInACVF.Section7
