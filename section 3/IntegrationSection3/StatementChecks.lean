module

public import IntegrationSection3.Atomicity

@[expose] public section

/-!
# Checks of the printed statements

Lemma 3.11 must exclude the empty relation: it is definable over every base,
lies in every product and has finite fibres for its first projection. This
check does not implement an author-approved correction of the headline.
-/

open Set FirstOrder

namespace IntegrationInACVF.Section3

variable {L : Language} {M : Type*} [L.Structure M]

/-- The three relation hypotheses printed in Lemma 3.11 hold for the empty
relation, regardless of the geometry or atomicity of the two factors. -/
theorem empty_relation_check (Q O C : Set M) :
    (∅ : Set (M × M)) ⊆ O ×ˢ C ∧ Q.Definable₂ L (∅ : Set (M × M)) ∧
      ∀ x : M, {y : M | (x,y) ∈ (∅ : Set (M × M))}.Finite := by
  refine ⟨Set.empty_subset _,?_,?_⟩
  · exact Set.definable_empty
  · intro x
    exact Set.finite_empty

end IntegrationInACVF.Section3
