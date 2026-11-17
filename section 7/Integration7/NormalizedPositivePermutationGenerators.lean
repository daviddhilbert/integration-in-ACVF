module

public import Integration7.NormalizedPositivePresentationGenerators
public import Integration7.NormalizedPositiveCoefficientActions
public import Integration7.AERVVolumePermutationLinearMaps
public import Integration7.PositiveVolumeClassProductExtensions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual VF coordinate permutations commute with positive coefficients
and give additive maps on positive normalized generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}

theorem ae_rv_volume_permute_base_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) (u : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPermuteBase hc C σ (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f) =
      aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u (aeRVVolumeFunctionPermuteBase hc C σ f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      rw [permuted_volume_family_row_class,selected_volume_family_left_product_row_class,
        positive_volume_class_extend_product hc (vfParameterVolumeContext C (x ∘ σ.symm))
          (vfParameterVolumeContext C x) (vf_parameter_volume_context_permutation_subset C σ x) (p := p) (q := k),
        selected_volume_family_left_product_row_class,permuted_volume_family_row_class]
      rfl

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedPositivePermutationGeneratorAddHom (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    PositiveDegreeGradedVolumeFunction hc C n →+ NormalizedVolumeFunction hc C n :=
  DirectSum.toAddMonoid (fun k => (normalizedVolumeFunctionGenerator hc C n).comp
    ((DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1)).comp
      (aeRVVolumeFunctionPermuteBaseOrdinaryLinearMap hc C σ k).toAddMonoidHom))

theorem normalized_positive_permutation_generator_of (n k : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (f : AERVVolumeFunction hc C n k) :
    normalizedPositivePermutationGeneratorAddHom hc C n σ
      (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) k f) =
    normalizedPositiveVolumeFunction hc C n k (aeRVVolumeFunctionPermuteBase hc C σ f) :=
  DirectSum.toAddMonoid_of _ k f

theorem normalized_positive_permutation_generator_positive_scalar (n p : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (u : PositiveVolumeBlowupClasses hc C p) (f : PositiveDegreeGradedVolumeFunction hc C n) :
    normalizedPositivePermutationGeneratorAddHom hc C n σ
      (DirectSum.of (RVVolumeBlowupClasses hc C) (p+1) u • f) =
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (p+1) u) •
      normalizedPositivePermutationGeneratorAddHom hc C n σ f := by
  induction f using DirectSum.induction_on with
  | zero => rw [smul_zero,map_zero,smul_zero]
  | add f g hf hg => rw [smul_add,map_add,hf,hg,map_add,smul_add]
  | of k f =>
    rw [graded_semiring_action_of_of ((aeVolumeFunctionGradedAction hc C n).shift 1),
      normalized_positive_permutation_generator_of,normalized_positive_permutation_generator_of]
    change normalizedPositiveVolumeFunction hc C n ((p+1)+k)
      (aeRVVolumeFunctionPermuteBase hc C σ (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f)) = _
    rw [ae_rv_volume_permute_base_positive_coefficient]
    exact normalized_positive_function_coefficient hc C n p k u _
end IntegrationInACVF.Section7
