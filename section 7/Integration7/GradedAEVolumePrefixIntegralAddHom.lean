import Integration7.GradedAEVolumeHeadIntegralAddHom
import Integration7.GradedAEVolumePrefixFubini

/-! Every actual iterated prefix partial integral is additive on the
full finite graded AE module, including ordinary degree-zero inputs. -/
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

theorem graded_ae_volume_prefix_integral_add : ∀ (r n : ℕ)
    (f g : GradedAEVolumeFunction hc C (n+r)),
    gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (f+g) =
      gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f +
      gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n g := by
  intro r
  induction r with
  | zero => intro n f g; rfl
  | succ r ih =>
    intro n f g
    rw [graded_ae_volume_prefix_integral_succ,graded_ae_volume_head_integral_add]
    exact ih n _ _

def gradedAEVolumePrefixIntegralAddHom (r n : ℕ) :
    GradedAEVolumeFunction hc C (n+r) →+ GradedAEVolumeFunction hc C n where
  toFun := gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
  map_zero' := (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n).map_zero
  map_add' := graded_ae_volume_prefix_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
end IntegrationInACVF.Section7
