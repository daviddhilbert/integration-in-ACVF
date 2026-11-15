import Integration7.AEOrdinaryPointHeadIntegrals
import Integration7.NormalizedVolumePrefixOperators
import Integration7.GradedAEVolumeHeadIntegralAddHom

/-! The normalized linear head operator agrees with the independently
constructed ordinary-input head map. It consequently agrees with the
actual full finite graded head and prefix maps on every generator. -/
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

theorem normalized_volume_head_integral_ordinary (n : ℕ) (f : AEOrdinaryRVVolumeFunction hc C (n+1)) :
    normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeFunctionGenerator hc C (n+1) (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) 0 f)) =
    normalizedPositiveVolumeFunction hc C n 0
      (aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  let u := positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M))
  let g := aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C (n+1) 0 u f
  let h := aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f
  have h₀ := congrArg (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)
    (normalized_ordinary_function_positive_generator hc C (n+1) f)
  have h₁ := normalized_volume_head_integral_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n 0 g
  have h₂ := congrArg (normalizedPositiveVolumeFunction hc C n 1)
    (ae_ordinary_point_product_head_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)
  have h₃ := normalized_positive_function_coefficient hc C n 0 0 u h
  have h₄ : normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) 1 u) •
      normalizedPositiveVolumeFunction hc C n 0 h=normalizedPositiveVolumeFunction hc C n 0 h := by
    change normalizedVolumeCoefficientMap hc C (volumePointClass hc C) • _ = _
    rw [normalized_volume_coefficient_point,one_smul]
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

theorem normalized_volume_head_integral_component (n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeFunctionGenerator hc C (n+1) (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f)) =
    normalizedVolumeFunctionGenerator hc C n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
        (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f)) := by
  cases j with
  | zero => exact normalized_volume_head_integral_ordinary hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f
  | succ k => exact normalized_volume_head_integral_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f

theorem normalized_volume_head_integral_generator (n : ℕ) (f : GradedAEVolumeFunction hc C (n+1)) :
    normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (normalizedVolumeFunctionGenerator hc C (n+1) f) =
    normalizedVolumeFunctionGenerator hc C n (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) := by
  induction f using DirectSum.induction_on with
  | zero => rw [map_zero,map_zero,map_zero,map_zero]
  | add f g hf hg => rw [map_add,map_add,hf,hg,graded_ae_volume_head_integral_add,map_add]
  | of j f =>
    rw [graded_ae_volume_head_integral_of]
    exact normalized_volume_head_integral_component hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f

theorem normalized_volume_prefix_integral_generator : ∀ (r n : ℕ) (f : GradedAEVolumeFunction hc C (n+r)),
    normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (normalizedVolumeFunctionGenerator hc C (n+r) f) =
    normalizedVolumeFunctionGenerator hc C n (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f) := by
  intro r
  induction r with
  | zero => intro n f; rfl
  | succ r ih =>
    intro n f
    have hHead := congrArg (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n)
      (normalized_volume_head_integral_generator hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f)
    exact hHead.trans (ih n (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f))
end IntegrationInACVF.Section7
