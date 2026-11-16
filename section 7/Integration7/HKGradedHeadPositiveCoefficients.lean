module

public import Integration7.HKAEZeroHeadPositiveCoefficients
public import Integration7.AERVVolumeHeadIntegralPositiveCoefficients
public import Integration7.HKGradedAEVolumeHeadFubini
public import Integration7.HKGradedAEVolumeActionCoherence
public import Integration7.HKGradedAEVolumePrefixFubini

@[expose] public section

/-! Every positive homogeneous coefficient commutes with the actual raw head and prefix integrals on the corrected finite graded function module, including its weighted-zero input component. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_volume_component_head_positive_coefficient (n p j : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n ((p+1)+j)
      (aeVolumeFunctionComponentCoefficientBiadditive hc C (n+1) (p+1) j u f) =
    aeVolumeFunctionComponentCoefficientBiadditive hc C n (p+1) (j+1) u
      (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) := by
  cases j with
  | zero => exact ae_zero_head_integral_positive_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 u f
  | succ k => exact ae_rv_volume_head_integral_positive_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 u f

theorem graded_ae_volume_head_positive_coefficient (n p : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (RVBlowupClasses hc C) (p+1) u • f) =
    DirectSum.of (RVBlowupClasses hc C) (p+1) u •
      gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  change gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (RVBlowupClasses hc C) (p+1) u • f) =
    DirectSum.of (RVBlowupClasses hc C) (p+1) u •
      gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f
  induction f using DirectSum.induction_on with
  | zero => rw [smul_zero,map_zero,smul_zero]
  | add f g hf hg => rw [smul_add,map_add,hf,hg,map_add,smul_add]
  | of j f =>
    change gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (RVBlowupClasses hc C) (p+1) u • DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f) =
      DirectSum.of (RVBlowupClasses hc C) (p+1) u •
        gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
          (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f)
    rw [graded_ae_volume_coefficient_action_of,graded_ae_volume_head_integral_of,
      graded_ae_volume_head_integral_of,graded_ae_volume_coefficient_action_of,
      ae_volume_component_head_positive_coefficient]
    rfl

theorem graded_ae_volume_prefix_positive_coefficient : ∀ (r n p : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : GradedAEVolumeFunction hc C (n+r)),
    gradedAEVolumePrefixIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
      (DirectSum.of (RVBlowupClasses hc C) (p+1) u • f) =
    DirectSum.of (RVBlowupClasses hc C) (p+1) u •
      gradedAEVolumePrefixIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f := by
  intro r
  induction r with
  | zero => intro n p u f; rfl
  | succ r ih =>
    intro n p u f
    change gradedAEVolumePrefixIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
      (gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r)
        (DirectSum.of (RVBlowupClasses hc C) (p+1) u • f)) = _
    rw [graded_ae_volume_head_positive_coefficient,ih]
    rfl
end IntegrationInACVF.Section7.HK
