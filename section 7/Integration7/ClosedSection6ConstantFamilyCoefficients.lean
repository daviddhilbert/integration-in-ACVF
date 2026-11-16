module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6ConstantRVFamilies
public import Integration7.ClosedSection6RVClassBaseChange
public import IntegrationSection6.ConstantFamilyCoefficients
public import IntegrationSection6.ConstantRVFamilies
public import IntegrationSection6.RVClassBaseChange

@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p k : ℕ}

theorem vfParameterCoefficientBase_real_contains (x : Fin p → VF (M := M)) :
    B.real ⊆ (vfParameterCoefficientBase B x).real :=
  Set.Subset.trans Set.subset_union_left
    (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).1

theorem constantRVSchema_represents (U : GammaObjectAt B Set.univ k) (x : Fin p → VF (M := M)) :
    gammaSchemaRepresents (U.changeBase (vfParameterCoefficientBase_real_contains x)
      (vfParameterCoefficientBase_gamma_contains x)).toGamma (constantRVSchema U p) (fun j => (x j).val) := by
  apply gammaSchemaRepresents_of_typed
  · exact constantRVSchema_domain U x
  · exact constantRVSchema_volume U x

theorem constantRVSchema_coefficient (P : IntegrationContext B κ hs) (U : GammaObjectAt B Set.univ k)
    (x : Fin p → VF (M := M)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical (constantRVSchema U p) x (constantRVSchema_finite U x) =
      P.scalarMap x (P.rvClass U) := by
  exact (schemaRowCoefficient_of_represents P x _ _ _ (constantRVSchema_represents U x)).trans
    (P.scalarMap_rvClass x U (vfParameterCoefficientBase_real_contains x) (vfParameterCoefficientBase_gamma_contains x)).symm

end IntegrationInACVF.Section7.CompletedSection6
