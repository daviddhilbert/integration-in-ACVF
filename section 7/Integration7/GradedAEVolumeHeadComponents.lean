module

public import Integration7.GradedAEVolumeHeadIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The full graded head map has no degree-zero output, and its degree
j+1 component is exactly the genuine head integral of input degree j. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem graded_ae_volume_head_integral_zero_component (n : ℕ) (f : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f 0 = 0 := by
  classical
  rw [graded_ae_volume_head_integral_sum,DFinsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact DirectSum.of_eq_of_ne _ _ _ (Nat.zero_ne_add_one j)

theorem graded_ae_volume_head_integral_component (n j : ℕ) (f : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f (j+1) =
      aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j (f j) := by
  classical
  rw [graded_ae_volume_head_integral_sum,DFinsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · exact DirectSum.of_eq_same _ _
  · intro i hi hij
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  · intro hj
    have hf : f j = 0 := DFinsupp.notMem_support_iff.mp hj
    rw [DirectSum.of_eq_same,hf,ae_volume_component_head_integral_zero]

end IntegrationInACVF.Section7
