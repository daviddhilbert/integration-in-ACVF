module

public import Integration7.GradedAEVolumeHeadIntegrals

@[expose] public section

/-! First-head Fubini for the full actual finite graded AE function
space, including ordinary degree zero, in the coefficient-first convention. -/
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

theorem graded_ae_volume_head_fubini_of (n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
          (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f)) =
      gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1)
        (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f) := by
  rw [graded_ae_volume_integral_of,graded_ae_volume_integral_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (by change n+(j+1)+1=(n+1+j)+1; omega)
    (ae_volume_component_head_fubini_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f))

theorem graded_ae_volume_head_fubini (n : ℕ) (f : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) =
      gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) f := by
  classical
  let I := gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  let J := gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1)
  calc
    I (gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) =
        ∑ j ∈ f.support, I (DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
          (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j (f j))) := by
      rw [graded_ae_volume_head_integral_sum]
      exact map_sum I _ _
    _ = ∑ j ∈ f.support, J (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j (f j)) :=
      Finset.sum_congr rfl (fun j _ => graded_ae_volume_head_fubini_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j (f j))
    _ = J (∑ j ∈ f.support, DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j (f j)) :=
      (map_sum J _ _).symm
    _ = J f := congrArg J (DirectSum.sum_support_of f)

end IntegrationInACVF.Section7
