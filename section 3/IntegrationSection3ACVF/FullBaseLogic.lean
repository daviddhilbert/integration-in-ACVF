import IntegrationSection3ACVF.FullBaseDefinability

/-! Boolean closure of actual full-base relations, with all free labels retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullBaseLogic

variable {M α : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [Finite α]

theorem implication (B : FullBaseAtomicity.Base (M := M))
    {P Q : Set (α → M)} (hP : FullBaseAtomicity.OverBase B P)
    (hQ : FullBaseAtomicity.OverBase B Q) :
    FullBaseAtomicity.OverBase B {z | z ∈ P → z ∈ Q} := by
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.union
    (FullBaseAtomicity.OverBase.compl hP) hQ)
  intro z
  change (¬ z ∈ P ∨ z ∈ Q) ↔ (z ∈ P → z ∈ Q)
  tauto

theorem equivalence (B : FullBaseAtomicity.Base (M := M))
    {P Q : Set (α → M)} (hP : FullBaseAtomicity.OverBase B P)
    (hQ : FullBaseAtomicity.OverBase B Q) :
    FullBaseAtomicity.OverBase B {z | z ∈ P ↔ z ∈ Q} := by
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter
    (implication B hP hQ) (implication B hQ hP))
  intro z
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩

theorem exists_finite {τ : Type} [Finite τ] (B : FullBaseAtomicity.Base (M := M))
    {P : τ → Set (α → M)} (hP : ∀ t, FullBaseAtomicity.OverBase B (P t)) :
    FullBaseAtomicity.OverBase B {z | ∃ t, z ∈ P t} := by
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.compl
    (FullBaseAtomicity.OverBase.forall_finite (fun t => FullBaseAtomicity.OverBase.compl (hP t))))
  intro z
  change (¬ ∀ t, z ∉ P t) ↔ _
  change (¬ ∀ t, z ∉ P t) ↔ ∃ t, z ∈ P t
  simp only [not_forall,not_not]

end IntegrationInACVF.Section3ACVF.FullBaseLogic
