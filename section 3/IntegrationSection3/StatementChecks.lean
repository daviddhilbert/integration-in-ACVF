module

public import IntegrationSection3.ParametricAtomicity

@[expose] public section

/-!
# Checks of the printed statements

Lemma 3.11 must exclude the empty relation: it is definable over every base,
lies in every product and has finite fibres for its first projection. This
check motivates the author-approved nonemptiness correction. Its logical
projection consequence is proved below; geometric separation remains open.
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

/-- The first step of the corrected Lemma 3.11: a nonempty definable
relation between two complete-type-generating sets projects onto both sets.
Nonemptiness is used to rule out the disjoint alternative on each side. -/
theorem complete_type_relation_projections (Q A B : Set M) (R : Set (M × M))
    (hA : GeneratesCompleteType L Q {z : Fin 1 → M | z 0 ∈ A})
    (hB : GeneratesCompleteType L Q {z : Fin 1 → M | z 0 ∈ B})
    (hR : Q.Definable₂ L R) (hsub : R ⊆ A ×ˢ B) (hne : R.Nonempty) :
    DefinableFamilies.domain R = A ∧ {b | ∃ a, (a,b) ∈ R} = B := by
  obtain ⟨⟨a,b⟩,hab⟩ := hne
  have ha : a ∈ A := (hsub hab).1
  have hb : b ∈ B := (hsub hab).2
  constructor
  · apply Set.Subset.antisymm
    · rintro x ⟨y,hxy⟩
      exact (hsub hxy).1
    · rcases hA {z | z 0 ∈ DefinableFamilies.domain R}
        (DefinableFamilies.definable_domain hR) with hw | hd
      · intro x hx
        exact hw (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ A} from hx)
      · exact (Set.disjoint_left.mp hd
          (show ![a] ∈ {z : Fin 1 → M | z 0 ∈ A} from ha)
          (show ![a] ∈ {z : Fin 1 → M | z 0 ∈ DefinableFamilies.domain R} from ⟨b,hab⟩)).elim
  · apply Set.Subset.antisymm
    · rintro y ⟨x,hxy⟩
      exact (hsub hxy).2
    · rcases hB {z | ∃ x, (x,z 0) ∈ R} (definable_range hR) with hw | hd
      · intro y hy
        exact hw (show ![y] ∈ {z : Fin 1 → M | z 0 ∈ B} from hy)
      · exact (Set.disjoint_left.mp hd
          (show ![b] ∈ {z : Fin 1 → M | z 0 ∈ B} from hb)
          (show ![b] ∈ {z : Fin 1 → M | ∃ x, (x,z 0) ∈ R} from ⟨a,hab⟩)).elim

end IntegrationInACVF.Section3
