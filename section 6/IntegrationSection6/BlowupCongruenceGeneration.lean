import IntegrationSection6.AdditiveCongruence
import IntegrationSection6.WholeBlowup

/-! The common-forward-blowup congruence is the least additive congruence
containing elementary replacements. Its definition remains the actual
geometric common-refinement relation. -/

noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}
variable (c : AddCon (RVKPlus (M := M) S k))
variable (hgen : ∀ (U : RVObject (M := M) S k) (i : Fin k), Admissible U i →
  c (rvClass U) (rvClass (elementary U i)))

include hgen

theorem Blowup.congruent {U V : RVObject (M := M) S k} (h : Blowup U V) :
    c (rvClass U) (rvClass V) := by
  rw [rvClass_iso h.source_split,rvClass_coprod,rvClass_iso h.result,rvClass_coprod]
  exact c.add (hgen h.center h.coordinate h.admissible) (c.refl _)

theorem IteratedBlowup.congruent {U V : RVObject (M := M) S k} {n : ℕ}
    (h : IteratedBlowup n U V) : c (rvClass U) (rvClass V) := by
  induction h with
  | zero he =>
    obtain ⟨e⟩ := he
    rw [rvClass_iso e]
    exact c.refl _
  | cons h _ ih => exact c.trans (h.congruent c hgen) ih

theorem Isp.congruent {U V : RVObject (M := M) S k} (h : Isp U V) :
    c (rvClass U) (rvClass V) := by
  obtain ⟨m,n,A,B,hu,hv,⟨e⟩⟩ := h
  have hU := hu.congruent c hgen
  have hV := hv.congruent c hgen
  rw [rvClass_iso e] at hU
  exact c.trans hU (c.symm hV)

/-- The universal property follows from finite actual forward witnesses. -/
theorem ispAddCon_least {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) : ispAddCon hκ hs hsmall ≤ c := by
  rintro a b ⟨U,V,rfl,rfl,h⟩
  exact h.congruent c hgen

end IntegrationInACVF.Section6
