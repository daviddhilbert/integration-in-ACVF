import IntegrationSection6.Blowups

/-! Degree zero admits no elementary chart, so common blowups reduce to
actual RV isomorphism, including the length-zero convention. -/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

 theorem no_blowup_degree_zero (U V : RVObject (M := M) S 0) : ¬ Nonempty (Blowup U V) := by
  rintro ⟨h⟩
  exact h.coordinate.elim0

theorem iteratedBlowup_degree_zero_iff (U V : RVObject (M := M) S 0) (n : ℕ) :
    IteratedBlowup n U V ↔ n = 0 ∧ Nonempty (U ≅ V) := by
  constructor
  · intro h
    cases h with
    | zero he => exact ⟨rfl,he⟩
    | cons h _ => exact h.coordinate.elim0
  · rintro ⟨rfl,he⟩
    exact .zero he

theorem isp_degree_zero_iff (U V : RVObject (M := M) S 0) : Isp U V ↔ Nonempty (U ≅ V) := by
  constructor
  · rintro ⟨m,n,A,B,hu,hv,⟨e⟩⟩
    obtain ⟨_,⟨f⟩⟩ := (iteratedBlowup_degree_zero_iff U A m).mp hu
    obtain ⟨_,⟨g⟩⟩ := (iteratedBlowup_degree_zero_iff V B n).mp hv
    exact ⟨f.trans (e.trans g.symm)⟩
  · rintro ⟨e⟩
    exact Isp.of_iso e

end IntegrationInACVF.Section6
