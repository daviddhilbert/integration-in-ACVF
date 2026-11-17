module

public import Integration7.AEOrdinaryHeadOrdinaryLinearity
public import Integration7.GradedHeadPositiveCoefficients

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual raw graded head integral is linear over the full graded
RV volume coefficient semiring, including both ordinary coefficient and
ordinary input degrees. Every homogeneous scalar law is proved geometrically. -/
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

theorem ae_volume_component_head_ordinary_smul (n j : ℕ)
    (z : RVVolumeBlowupClasses hc C 0) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j (z • f) =
      z • aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f := by
  cases j with
  | zero => exact ae_ordinary_head_integral_ordinary_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 z f
  | succ k => exact ae_rv_volume_head_integral_ordinary_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 z f

theorem ae_volume_component_head_degree_heq (n : ℕ) {i j : ℕ} (h : i=j)
    {f : AEVolumeFunctionComponent hc C (n+1) i} {g : AEVolumeFunctionComponent hc C (n+1) j}
    (he : HEq f g) :
    HEq (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n i f)
      (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j g) := by
  cases h
  cases he
  rfl

theorem ae_volume_component_head_zero_coefficient (n j : ℕ)
    (z : RVVolumeBlowupClasses hc C 0) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (0+j)
      (aeVolumeFunctionComponentCoefficientBiadditive hc C (n+1) 0 j z f) =
    aeVolumeFunctionComponentCoefficientBiadditive hc C n 0 (j+1) z
      (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) := by
  have hL := ae_volume_component_head_degree_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (Nat.zero_add j)
    (ae_volume_component_zero_coefficient_heq hc C (n+1) j z f)
  exact eq_of_heq (hL.trans ((heq_of_eq
    (ae_volume_component_head_ordinary_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j z f)).trans
      (ae_volume_component_zero_coefficient_heq hc C n (j+1) z _).symm))

theorem graded_ae_volume_head_zero_coefficient (n : ℕ)
    (z : RVVolumeBlowupClasses hc C 0) (f : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (RVVolumeBlowupClasses hc C) 0 z • f) =
    DirectSum.of (RVVolumeBlowupClasses hc C) 0 z •
      gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  change gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (RVVolumeBlowupClasses hc C) 0 z • f) =
    DirectSum.of (RVVolumeBlowupClasses hc C) 0 z •
      gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f
  induction f using DirectSum.induction_on with
  | zero => rw [smul_zero,map_zero,smul_zero]
  | add f g hf hg => rw [smul_add,map_add,hf,hg,map_add,smul_add]
  | of j f =>
    change gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (RVVolumeBlowupClasses hc C) 0 z • DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f) =
      DirectSum.of (RVVolumeBlowupClasses hc C) 0 z •
        gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
          (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f)
    rw [graded_ae_volume_coefficient_action_of,graded_ae_volume_head_integral_of,
      graded_ae_volume_head_integral_of,graded_ae_volume_coefficient_action_of,
      ae_volume_component_head_zero_coefficient]
    rfl

def gradedAEVolumeHeadIntegralLinearMap (n : ℕ) :
    GradedAEVolumeFunction hc C (n+1) →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C n where
  toAddHom := gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  map_smul' r f := by
    change gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (r • f) =
      r • gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f
    induction r using DirectSum.induction_on with
    | zero => rw [zero_smul,map_zero,zero_smul]
    | add r s hr hs => rw [add_smul,map_add,hr,hs,add_smul]
    | of i u =>
      cases i with
      | zero => exact graded_ae_volume_head_zero_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n u f
      | succ p => exact graded_ae_volume_head_positive_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n p u f
end IntegrationInACVF.Section7
