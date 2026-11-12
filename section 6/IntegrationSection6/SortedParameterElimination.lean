import Section3.AlgebraicTransitivity

/-! Parameter elimination uses the finitely many sorted names in the
witness formula; arbitrary unused elements of a raw base need no sort. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Eliminate algebraic parameters without requiring all elements of the
possibly unsorted parameter base to belong to a sort. -/
theorem algebraicAt_eliminate_sorted_parameters {S B : Set M} {σ : SortTag} {x : M}
    (hx : AlgebraicAt B σ x)
    (hB : ∀ b ∈ B, ∀ τ, sortEval τ b → AlgebraicAt S τ b) :
    AlgebraicAt S σ x := by
  obtain ⟨s, ⟨⟨p, φ, hφ, he⟩, hs⟩, hf, hx⟩ := hx
  let q : Parameters (Set.range p.values) :=
    { p with mem_base := fun i => Set.mem_range_self i }
  have hd : DefinableAt (Set.range p.values) σ s :=
    ⟨⟨q, φ, hφ, he⟩, hs⟩
  apply (show AlgebraicAt (Set.range p.values) σ x from ⟨s, hd, hf, hx⟩).eliminate_algebraic_params
  rintro b ⟨i, rfl⟩
  exact ⟨p.sorts i, hB _ (p.mem_base i) _ (p.sorted i)⟩

end IntegrationInACVF.Section6
