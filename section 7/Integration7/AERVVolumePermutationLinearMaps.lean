module

public import Integration7.PositiveVolumeClassScalarExtensions
public import Integration7.AERVVolumeOrdinaryCoefficientModules
public import Integration7.AERVVolumePermutedFunctions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Reindexing VF coordinates is linear on positive AE functions over
ordinary coefficients. The proof uses the actual permuted-row isomorphisms
and semilinear parameter extension, with no volume-permutation assertion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem permuted_volume_family_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.permuteBase σ).rowInContext x) =
      positiveVolumeClassExtend hc (vfParameterVolumeContext C (x ∘ σ.symm)) (vfParameterVolumeContext C x)
        (vf_parameter_volume_context_permutation_subset C σ x) k
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C (x ∘ σ.symm)) (F.rowInContext (x ∘ σ.symm))) :=
  positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x) (permutedVolumeFamilyRowIso hc F σ x)

theorem ae_rv_volume_permute_base_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) (f g : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPermuteBase hc C σ (f+g) =
      aeRVVolumeFunctionPermuteBase hc C σ f + aeRVVolumeFunctionPermuteBase hc C σ g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      rw [permuted_volume_family_row_class,selected_volume_family_sum_row_class,
        selected_volume_family_sum_row_class,permuted_volume_family_row_class,permuted_volume_family_row_class]
      exact map_add _ _ _

theorem ae_rv_volume_permute_base_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) : aeRVVolumeFunctionPermuteBase hc C (k := k) σ 0 = 0 := by
  apply Quotient.sound
  apply ae_rv_volume_function_equivalent_of_pointwise hc C
  intro x
  rw [permuted_volume_family_row_class,selected_zero_volume_family_row_class,selected_zero_volume_family_row_class]
  exact map_zero _

theorem ae_rv_volume_permute_base_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) (z : RVVolumeBlowupClasses hc C 0) (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPermuteBase hc C σ (z • f) = z • aeRVVolumeFunctionPermuteBase hc C σ f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      rw [permuted_volume_family_row_class,volume_family_zero_product_row_scalar,
        volume_family_zero_product_row_scalar,positive_volume_class_extend_smul,
        ordinary_volume_coefficient_extend_trans,permuted_volume_family_row_class]

def aeRVVolumeFunctionPermuteBaseOrdinaryLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (n+1))) (k : ℕ) :
    AERVVolumeFunction hc C n k →ₗ[RVVolumeBlowupClasses hc C 0] AERVVolumeFunction hc C n k where
  toFun := aeRVVolumeFunctionPermuteBase hc C σ
  map_add' := ae_rv_volume_permute_base_add hc C σ
  map_smul' := ae_rv_volume_permute_base_smul hc C σ

end IntegrationInACVF.Section7
