module

public import Integration7.GradedHeadIntegralLinearMaps

@[expose] public section

/-! Successive raw head integrals give linear prefix integrals on the
full finite graded module over the full graded coefficient semiring.
Their underlying maps are exactly the existing geometric operators. -/
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

def gradedAEVolumePrefixIntegralLinearMap : (r n : ℕ) →
    GradedAEVolumeFunction hc C (n+r) →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C n
  | 0,_ => LinearMap.id
  | r+1,n => (gradedAEVolumePrefixIntegralLinearMap r n).comp
      (gradedAEVolumeHeadIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r))

theorem graded_ae_volume_prefix_linear_value : ∀ (r n : ℕ) (f : GradedAEVolumeFunction hc C (n+r)),
    gradedAEVolumePrefixIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f =
      gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f := by
  intro r
  induction r with
  | zero => intro n f; rfl
  | succ r ih =>
    intro n f
    exact ih n (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f)

theorem graded_ae_volume_prefix_smul (r n : ℕ) (u : RVVolumeBlowupSemiring hc C)
    (f : GradedAEVolumeFunction hc C (n+r)) :
    gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (u • f) =
      u • gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f := by
  rw [← graded_ae_volume_prefix_linear_value,← graded_ae_volume_prefix_linear_value,map_smul]

theorem graded_ae_volume_prefix_linear_fubini (r n : ℕ) (f : GradedAEVolumeFunction hc C (n+r)) :
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (gradedAEVolumePrefixIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f) =
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f := by
  rw [graded_ae_volume_prefix_linear_value]
  exact graded_ae_volume_prefix_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f
end IntegrationInACVF.Section7
