import Integration7.FiniteVolumeParameterContexts

/-! Two genuine small containing contexts admit a genuine common small
containing context. Their model cardinal bounds may differ. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M]

theorem volume_context_join_exists (C D : BaseContext M) :
    ∃ E : BaseContext M, (C.base : Set M) ⊆ (E.base : Set M) ∧ (D.base : Set M) ⊆ (E.base : Set M) := by
  wlog h : C.κ ≤ D.κ generalizing C D
  · obtain ⟨E,hDE,hCE⟩ := this D C (le_of_not_ge h)
    exact ⟨E,hCE,hDE⟩
  let S : Set M := (C.base : Set M) ∪ (D.base : Set M)
  have hS : Cardinal.mk S < D.κ := (Cardinal.mk_union_le (C.base : Set M) (D.base : Set M)).trans_lt
    (Cardinal.add_lt_of_lt D.uncountable.le (C.small.trans_le h) D.small)
  let E : BaseContext M := {
    model00 := D.model00
    κ := D.κ
    uncountable := D.uncountable
    saturated := D.saturated
    homogeneous := D.homogeneous
    base := Substructure.closure LRV S
    small := small_generated_substructure D.uncountable S hS
    nontrivial_values := by
      obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := D.nontrivial_values
      exact ⟨⟨a.val,Substructure.subset_closure (Or.inr a.property)⟩,
        ⟨b.val,Substructure.subset_closure (Or.inr b.property)⟩,ha,hb,ha0,hb0,hab⟩ }
  exact ⟨E,fun _ hx => Substructure.subset_closure (Or.inl hx),
    fun _ hx => Substructure.subset_closure (Or.inr hx)⟩

end IntegrationInACVF.Section7
