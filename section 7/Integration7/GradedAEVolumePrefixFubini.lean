import Integration7.GradedAEVolumeHeadFubini

/-! Integrating any VF prefix leaves a genuine full finite graded AE
function on the nonempty retained base and satisfies exact total Fubini. -/
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

def gradedAEVolumePrefixIntegral : (r n : ℕ) →
    ZeroHom (GradedAEVolumeFunction hc C (n+r)) (GradedAEVolumeFunction hc C n)
  | 0,n => ZeroHom.id _
  | r+1,n => (gradedAEVolumePrefixIntegral r n).comp
      (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r))

theorem graded_ae_volume_prefix_integral_zero (n : ℕ) (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 0 n f = f := rfl

theorem graded_ae_volume_prefix_integral_succ (r n : ℕ) (f : GradedAEVolumeFunction hc C (n+(r+1))) :
    gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (r+1) n f =
      gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
        (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f) := rfl

theorem graded_ae_volume_prefix_fubini : ∀ (r n : ℕ) (f : GradedAEVolumeFunction hc C (n+r)),
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f) =
      gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f := by
  intro r
  induction r with
  | zero => intro n f; rfl
  | succ r ih =>
    intro n f
    exact (ih n (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f)).trans
      (graded_ae_volume_head_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f)

end IntegrationInACVF.Section7
