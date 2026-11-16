module

public import Integration7.OrdinaryPositivePermutationCompatibility
public import Integration7.GradedAEVolumeActionCoherence
public import Integration7.GradedSemiringActionLinearMaps

@[expose] public section

/-! The genuine VF coordinate permutation on every raw graded AE
component is linear over the full graded RV volume coefficient semiring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ)

def aeVolumeFunctionComponentPermutationLinearMap (σ : Equiv.Perm (Fin (n+1))) (j : ℕ) :
    AEVolumeFunctionComponent hc C n j →ₗ[RVVolumeBlowupClasses hc C 0]
      AEVolumeFunctionComponent hc C n j := by
  cases j with
  | zero => exact aeOrdinaryRVVolumeFunctionPermuteBaseLinearMap hc C σ
  | succ k => exact aeRVVolumeFunctionPermuteBaseOrdinaryLinearMap hc C σ k

theorem ae_volume_component_permutation_degree_heq (σ : Equiv.Perm (Fin (n+1)))
    {i j : ℕ} (h : i=j) {f : AEVolumeFunctionComponent hc C n i}
    {g : AEVolumeFunctionComponent hc C n j} (he : HEq f g) :
    HEq (aeVolumeFunctionComponentPermutationLinearMap hc C n σ i f)
      (aeVolumeFunctionComponentPermutationLinearMap hc C n σ j g) := by
  cases h
  cases he
  rfl

theorem ae_volume_component_permutation_coefficient (σ : Equiv.Perm (Fin (n+1)))
    (i j : ℕ) (u : RVVolumeBlowupClasses hc C i) (f : AEVolumeFunctionComponent hc C n j) :
    aeVolumeFunctionComponentPermutationLinearMap hc C n σ (i+j)
      (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f) =
      aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u
        (aeVolumeFunctionComponentPermutationLinearMap hc C n σ j f) := by
  cases i with
  | zero =>
    have hL := ae_volume_component_permutation_degree_heq hc C n σ (Nat.zero_add j)
      (ae_volume_component_zero_coefficient_heq hc C n j u f)
    exact eq_of_heq (hL.trans ((heq_of_eq
      ((aeVolumeFunctionComponentPermutationLinearMap hc C n σ j).map_smul u f)).trans
        (ae_volume_component_zero_coefficient_heq hc C n j u _).symm))
  | succ p =>
    cases j with
    | zero => exact ae_ordinary_permute_base_positive_coefficient hc C σ u f
    | succ k => exact ae_rv_volume_permute_base_positive_coefficient hc C σ u f

def gradedAEVolumePermutationLinearMap (σ : Equiv.Perm (Fin (n+1))) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C n :=
  gradedSemiringActionLinearMap (aeVolumeFunctionGradedAction hc C n) (aeVolumeFunctionGradedAction hc C n)
    (fun j => (aeVolumeFunctionComponentPermutationLinearMap hc C n σ j).toAddMonoidHom)
    (ae_volume_component_permutation_coefficient hc C n σ)

theorem graded_ae_volume_permutation_of (σ : Equiv.Perm (Fin (n+1))) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) :
    gradedAEVolumePermutationLinearMap hc C n σ (DirectSum.of (AEVolumeFunctionComponent hc C n) j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) j
        (aeVolumeFunctionComponentPermutationLinearMap hc C n σ j f) :=
  graded_component_map_to_sum_of
    (fun t => (aeVolumeFunctionComponentPermutationLinearMap hc C n σ t).toAddMonoidHom) j f
end IntegrationInACVF.Section7
