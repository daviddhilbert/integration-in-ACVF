import Integration7.AEOrdinaryVolumePermutations
import Integration7.NormalizedPositivePermutationGenerators

/-! Coordinate permutation commutes with a positive coefficient acting
on an ordinary-valued function. No normalization relation is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}

theorem ae_ordinary_permute_base_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) (u : PositiveVolumeBlowupClasses hc C p)
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeRVVolumeFunctionPermuteBase hc C σ (aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u f) =
      aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u
        (aeOrdinaryRVVolumeFunctionPermuteBase hc C σ f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      rw [permuted_volume_family_row_class,selected_ordinary_family_positive_product_row_class,
        positive_volume_class_extend_smul,selected_ordinary_family_positive_product_row_class,
        permuted_ordinary_volume_family_row_class]
      rfl
end IntegrationInACVF.Section7
