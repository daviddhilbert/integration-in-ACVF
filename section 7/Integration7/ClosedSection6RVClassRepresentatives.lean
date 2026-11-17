module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6ContextRVClasses
public import IntegrationSection6.RVClassRepresentatives
public import IntegrationSection6.ContextRVClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
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
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

theorem IntegrationContext.rvClass_representative (P : IntegrationContext B κ hs) (r : P.RV) :
    ∃ k, ∃ U : GammaObjectAt B Set.univ k, P.rvClass U = r := by
  obtain ⟨a,rfl⟩ := (gammaNonzeroIspUnionRingCon P.countable_le hs P.characteristic P.real_small P.field_base
    P.gamma_small P.value P.value_mem P.value_large P.canonical P.generated).mk'_surjective r
  obtain ⟨k,x,rfl⟩ := gammaThroughToGradedAt_exhaustive a
  obtain ⟨U,hU⟩ := gammaIsoClassAt_surjective (gammaFiniteWeightAssemblyAt k x)
  refine ⟨k,U,?_⟩
  change (gammaNonzeroIspUnionRingCon P.countable_le hs P.characteristic P.real_small P.field_base
    P.gamma_small P.value P.value_mem P.value_large P.canonical P.generated).mk'
    (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) = _
  rw [hU,gammaNonzeroResolutionAt_assembly]

def IntegrationContext.rvRepresentative (P : IntegrationContext B κ hs) (r : P.RV) :
    Σ k, GammaObjectAt B Set.univ k :=
  ⟨(P.rvClass_representative r).choose,((P.rvClass_representative r).choose_spec).choose⟩

theorem IntegrationContext.rvRepresentative_class (P : IntegrationContext B κ hs) (r : P.RV) :
    P.rvClass (P.rvRepresentative r).2 = r := ((P.rvClass_representative r).choose_spec).choose_spec

end IntegrationInACVF.Section7.CompletedSection6
