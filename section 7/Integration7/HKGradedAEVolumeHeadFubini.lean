import Integration7.HKAEVolumeComponentHeadIntegrals

/-! Actual weighted-zero and positive homogeneous head maps assemble
into an additive operator on all finite graded functions and satisfy Fubini. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def gradedAEVolumeHeadIntegralAddHom (n : ℕ) :
    GradedAEVolumeFunction hc C (n+1) →+ GradedAEVolumeFunction hc C n :=
  DirectSum.toAddMonoid (fun j =>
    (DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)).comp
      (aeVolumeComponentHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j))

theorem graded_ae_volume_head_integral_of (n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
        (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) := by
  change DirectSum.toAddMonoid _ ((DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j) f) = _
  rw [DirectSum.toAddMonoid_of]
  cases j <;> rfl

theorem graded_ae_volume_head_fubini_of (n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
        (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f)) =
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1)
      (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f) := by
  rw [graded_ae_volume_integral_of,graded_ae_volume_integral_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (by change n+(j+1)+1=(n+1+j)+1; omega)
    (ae_volume_component_head_fubini_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f))

theorem graded_ae_volume_head_fubini (n : ℕ) (f : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) =
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) f := by
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp only [map_zero]
  · intro j x
    rw [graded_ae_volume_head_integral_of]
    exact graded_ae_volume_head_fubini_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j x
  · intro x y hx hy
    simp only [map_add,hx,hy]

end IntegrationInACVF.Section7.HK
