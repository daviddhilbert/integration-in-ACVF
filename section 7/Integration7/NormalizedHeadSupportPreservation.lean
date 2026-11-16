module

public import Integration7.NormalizedSupportedHeadIntegrals
public import Integration7.NormalizedVolumeHeadFubini
public import Integration7.NormalizedSupportedVolumeIntegrals

@[expose] public section

/-! Head integration carries every supported normalized function to
its actual projected support and preserves the supported total integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_volume_head_preserves_support
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M))
    (f : NormalizedVolumeFunction hc C (n+1)) (hf : HasNormalizedVolumeSupport hc C X f) :
    HasNormalizedVolumeSupport hc C (pureVFCoordinateImage X Fin.succ)
      (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) := by
  obtain ⟨g,rfl⟩ := hf
  exact ⟨normalizedSupportedHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X g,
    LinearMap.congr_fun (normalized_supported_head_integral_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X) g⟩

theorem normalized_supported_head_total_fubini
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M)) :
    (normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X Fin.succ)).comp
      (normalizedSupportedHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X) =
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X Fin.succ)
      (normalizedSupportedHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f)) = _
  exact (congrArg (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)
    (LinearMap.congr_fun (normalized_supported_head_integral_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X) f)).trans
    (LinearMap.congr_fun (normalized_volume_head_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)
      (normalizedSupportedVolumeForget hc C X f))
end IntegrationInACVF.Section7
