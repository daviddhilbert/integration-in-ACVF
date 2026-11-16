module

public import Integration7.AEOrdinaryVolumeHeadFubini
public import Integration7.AppendedVolumeHeadFubini
public import Integration7.GradedAEVolumeIntegralComponents

@[expose] public section

/-! First-head integration raises every homogeneous coefficient degree
by one, including ordinary degree zero. Each component satisfies Fubini. -/
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

def aeVolumeFunctionComponentHeadIntegral (n j : ℕ) :
    AEVolumeFunctionComponent hc C (n+1) j → AEVolumeFunctionComponent hc C n (j+1) := by
  cases j with
  | zero => exact aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  | succ k => exact aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1

theorem ae_volume_component_head_integral_ordinary (n : ℕ) (f : AEOrdinaryRVVolumeFunction hc C (n+1)) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n 0 f =
      aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := rfl

theorem ae_volume_component_head_integral_positive (n k : ℕ) (f : AERVVolumeFunction hc C (n+1) k) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (k+1) f =
      aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := rfl

theorem ae_volume_component_head_fubini_heq (n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    HEq (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (j+1)
        (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f))
      (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) j f) := by
  cases j with
  | zero =>
    exact (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n 0
      (aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)).trans
      (ae_ordinary_rv_volume_function_appended_head_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)
  | succ k =>
    exact (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (k+1)
      (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)).trans
      ((heq_of_eq (ae_rv_volume_function_appended_head_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)).trans
        (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) k f).symm)

end IntegrationInACVF.Section7
