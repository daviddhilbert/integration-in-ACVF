module

public import Integration7.HKAEZeroHeadFubini
public import Integration7.HKAEZeroHeadIntegralAdditivity
public import Integration7.AERVVolumeHeadIntegralAdditivity
public import Integration7.AppendedVolumeHeadFubini
public import Integration7.HKGradedAEVolumeIntegralAddHoms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! First-head integration raises every homogeneous coefficient degree
by one, including weighted degree zero. Each component satisfies Fubini. -/
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

def aeVolumeFunctionComponentHeadIntegral (n j : ℕ) :
    AEVolumeFunctionComponent hc C (n+1) j → AEVolumeFunctionComponent hc C n (j+1) := by
  cases j with
  | zero => exact aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  | succ k => exact aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1

theorem ae_volume_component_head_integral_zero (n : ℕ) (f : AEZeroVolumeFunction hc C (n+1)) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n 0 f =
      aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := rfl

theorem ae_volume_component_head_integral_positive (n k : ℕ) (f : AERVVolumeFunction hc C (n+1) k) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (k+1) f =
      aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := rfl

def aeVolumeComponentHeadIntegralAddHom (n j : ℕ) :
    AEVolumeFunctionComponent hc C (n+1) j →+ AEVolumeFunctionComponent hc C n (j+1) := by
  cases j with
  | zero => exact aeZeroVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  | succ k => exact aeRVVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k

theorem ae_volume_component_head_fubini_heq (n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    HEq (aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (j+1)
        (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f))
      (aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) j f) := by
  cases j with
  | zero =>
    exact (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n 0
      (aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)).trans
      (ae_zero_volume_function_appended_head_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)
  | succ k =>
    exact (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (k+1)
      (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)).trans
      ((heq_of_eq (ae_rv_volume_function_appended_head_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)).trans
        (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) k f).symm)

end IntegrationInACVF.Section7.HK
