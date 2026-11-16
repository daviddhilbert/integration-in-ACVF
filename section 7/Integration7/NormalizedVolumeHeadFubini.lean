module

public import Integration7.NormalizedVolumeHeadOperators
public import Integration7.GradedAEVolumeHeadFubini

@[expose] public section

/-! Integrating the actual normalized head operator and then the
remaining coordinates equals the total integral on every normalized
function, by positive generation and the geometric head theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_volume_head_total_fubini (n : ℕ) :
    (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
      (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) := by
  apply normalized_volume_function_linearMap_ext_positive hc C (n+1)
  intro k f
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C (n+1) k f)) = _
  rw [normalized_volume_head_integral_positive]
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedVolumeFunctionGenerator hc C n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) ((k+1)+1)
        (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f))) = _
  rw [normalized_volume_integral_generator]
  change _ = normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1)
    (normalizedVolumeFunctionGenerator hc C (n+1) (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) (k+1) f))
  rw [normalized_volume_integral_generator]
  exact congrArg (normalizedVolumeCoefficientMap hc C)
    (graded_ae_volume_head_fubini_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (k+1) f)

theorem normalized_volume_head_total_value (n : ℕ) (f : NormalizedVolumeFunction hc C (n+1)) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) f :=
  LinearMap.congr_fun (normalized_volume_head_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n) f
end IntegrationInACVF.Section7
