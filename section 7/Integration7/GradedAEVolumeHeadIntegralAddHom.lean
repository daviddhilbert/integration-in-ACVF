module

public import Integration7.AEVolumeHeadIntegralAddHom
public import Integration7.GradedAEVolumeHeadComponents

@[expose] public section

/-! The existing finite graded head integral is additive on the entire
function module; its actual homogeneous components determine equality. -/
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

theorem graded_ae_volume_head_integral_add (n : ℕ)
    (f g : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (f+g) =
      gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f +
      gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n g := by
  apply DFinsupp.ext
  intro j
  cases j with
  | zero => simp only [DirectSum.add_apply,graded_ae_volume_head_integral_zero_component,add_zero]
  | succ j =>
    simp only [DirectSum.add_apply,graded_ae_volume_head_integral_component]
    exact ae_volume_component_head_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j _ _

def gradedAEVolumeHeadIntegralAddHom (n : ℕ) :
    GradedAEVolumeFunction hc C (n+1) →+ GradedAEVolumeFunction hc C n where
  toFun := gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  map_zero' := (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).map_zero
  map_add' := graded_ae_volume_head_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
end IntegrationInACVF.Section7
