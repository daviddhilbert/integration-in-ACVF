import IntegrationSection6.ContextRVClasses

/-! Every coefficient class has one actual representative in RV[k] for
some finite k, by finite-support assembly of its nonzero grading. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

theorem IntegrationContext.rvClass_representative (P : IntegrationContext B κ hs) (r : P.RV) :
    ∃ k, ∃ U : GammaObjectAt B Set.univ k, P.rvClass U = r := by
  obtain ⟨a,rfl⟩ := (gammaNonzeroIspUnionRingCon P.countable_le hs P.characteristic P.real_small P.field_base
    P.gamma_small P.value P.value_mem P.value_large P.section5_two_order P.generated).mk'_surjective r
  obtain ⟨k,x,rfl⟩ := gammaThroughToGradedAt_exhaustive a
  obtain ⟨U,hU⟩ := gammaIsoClassAt_surjective (gammaFiniteWeightAssemblyAt k x)
  refine ⟨k,U,?_⟩
  change (gammaNonzeroIspUnionRingCon P.countable_le hs P.characteristic P.real_small P.field_base
    P.gamma_small P.value P.value_mem P.value_large P.section5_two_order P.generated).mk'
    (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) = _
  rw [hU,gammaNonzeroResolutionAt_assembly]

def IntegrationContext.rvRepresentative (P : IntegrationContext B κ hs) (r : P.RV) :
    Σ k, GammaObjectAt B Set.univ k :=
  ⟨(P.rvClass_representative r).choose,((P.rvClass_representative r).choose_spec).choose⟩

theorem IntegrationContext.rvRepresentative_class (P : IntegrationContext B κ hs) (r : P.RV) :
    P.rvClass (P.rvRepresentative r).2 = r := ((P.rvClass_representative r).choose_spec).choose_spec

end IntegrationInACVF.Section6.FiniteRV
