import Integration7.AERVVolumeHeadIntegralAdditivity
import Integration7.AEOrdinaryHeadIntegralAdditivity

/-! Every actual homogeneous head map, including ordinary degree zero,
is an additive homomorphism with output degree raised by one. -/
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

theorem ae_volume_component_head_integral_add (n j : ℕ)
    (f g : AEVolumeFunctionComponent hc C (n+1) j) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j (f+g) =
      aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f +
      aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j g := by
  cases j with
  | zero => exact ae_ordinary_rv_volume_head_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f g
  | succ k => exact ae_rv_volume_head_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f g

def aeVolumeComponentHeadIntegralAddHom (n j : ℕ) :
    AEVolumeFunctionComponent hc C (n+1) j →+ AEVolumeFunctionComponent hc C n (j+1) where
  toFun := aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
  map_zero' := ae_volume_component_head_integral_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
  map_add' := ae_volume_component_head_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
end IntegrationInACVF.Section7
