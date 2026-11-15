import Integration7.NormalizedPrefixSupportPreservation

/-! Prefix integration on the supported normalized function spaces.
The target is the literal projected support and forgetting support
recovers the unchanged full prefix operator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedSupportedPrefixIntegral (r n : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M)) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedSupportedVolumeFunction hc C (pureVFPrefixImage r n X) :=
  (normalizedVolumeRestriction hc C (pureVFPrefixImage r n X)).comp
    ((normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n).comp
      (normalizedSupportedVolumeForget hc C X))

theorem normalized_supported_prefix_integral_forget (r n : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M)) :
    (normalizedSupportedVolumeForget hc C (pureVFPrefixImage r n X)).comp
      (normalizedSupportedPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n X) =
    (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n).comp
      (normalizedSupportedVolumeForget hc C X) := by
  apply LinearMap.ext
  intro f
  exact (normalized_volume_support_iff_projection hc C _ _).mp
    (normalized_volume_prefix_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n X
      (normalizedSupportedVolumeForget hc C X f) (normalized_supported_volume_has_support hc C X f))

theorem normalized_supported_prefix_total_fubini (r n : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M)) :
    (normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFPrefixImage r n X)).comp
      (normalizedSupportedPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n X) =
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  exact (congrArg (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)
    (LinearMap.congr_fun (normalized_supported_prefix_integral_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n X) f)).trans
    (normalized_volume_prefix_total_value hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
      (normalizedSupportedVolumeForget hc C X f))
end IntegrationInACVF.Section7
