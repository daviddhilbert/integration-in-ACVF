import IntegrationSection6.Confluence
import Section4.RVPositiveIsoComparison
import Mathlib.GroupTheory.Congruence.Basic

/-! The additive congruence assertion of Lemma 6.8 on the actual RV quotient. -/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

/-- Add an unchanged summand to a single actual blowup. -/
def Blowup.coprodRight {U V : RVObject (M := M) S k} (h : Blowup U V)
    (R : RVObject (M := M) S k) : Blowup (rvCoprodObject U R) (rvCoprodObject V R) := by
  let T := U.restrict (complement U h.locus) (complement_subset U h.locus)
  have hes : Nonempty (rvCoprodObject U R ≅ rvCoprodObject h.center (rvCoprodObject T R)) := by
    apply rvIsoClass_eq_iff.mp
    rw [rvIsoClass_coprod, rvIsoClass_iso h.source_split]
    simp only [rvIsoClass_coprod]
    abel
  have het : Nonempty (rvCoprodObject V R ≅
      rvCoprodObject (elementary h.center h.coordinate) (rvCoprodObject T R)) := by
    apply rvIsoClass_eq_iff.mp
    rw [rvIsoClass_coprod, rvIsoClass_iso h.result]
    simp only [rvIsoClass_coprod]
    abel
  exact Blowup.of_split h.coordinate h.admissible (Classical.choice hes) (Classical.choice het)

theorem IteratedBlowup.coprodRight {U V : RVObject (M := M) S k} {n : ℕ}
    (h : IteratedBlowup n U V) (R : RVObject (M := M) S k) :
    IteratedBlowup n (rvCoprodObject U R) (rvCoprodObject V R) := by
  induction h with
  | zero he => exact .zero (he.map (fun e => rvCoprodIso e (Iso.refl R)))
  | cons h _ ih => exact .cons (h.coprodRight R) ih

theorem Isp.coprodRight {U V : RVObject (M := M) S k} (h : Isp U V)
    (R : RVObject (M := M) S k) : Isp (rvCoprodObject U R) (rvCoprodObject V R) := by
  obtain ⟨m, n, A, B, hu, hv, he⟩ := h
  exact ⟨m, n, rvCoprodObject A R, rvCoprodObject B R,
    hu.coprodRight R, hv.coprodRight R, he.map (fun e => rvCoprodIso e (Iso.refl R))⟩

theorem Isp.coprodLeft {U V : RVObject (M := M) S k} (h : Isp U V)
    (R : RVObject (M := M) S k) : Isp (rvCoprodObject R U) (rvCoprodObject R V) := by
  have eU : Nonempty (rvCoprodObject R U ≅ rvCoprodObject U R) := by
    apply rvIsoClass_eq_iff.mp
    simp only [rvIsoClass_coprod]
    exact add_comm _ _
  have eV : Nonempty (rvCoprodObject R V ≅ rvCoprodObject V R) := by
    apply rvIsoClass_eq_iff.mp
    simp only [rvIsoClass_coprod]
    exact add_comm _ _
  obtain ⟨e⟩ := eU
  obtain ⟨f⟩ := eV
  exact (h.coprodRight R).corollary_6_6 e f

theorem Isp.coprod {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V R T : RVObject (M := M) S k} (h : Isp U V) (g : Isp R T) :
    Isp (rvCoprodObject U R) (rvCoprodObject V T) :=
  (h.coprodRight R).trans hκ hs hsmall (g.coprodLeft V)

/-- The relation induced on the inherited actual positive scissor quotient.
Its independence of representatives is proved by Corollary 6.6. -/
def positiveIsp (a b : RVKPlus (M := M) S k) : Prop :=
  ∃ U V : RVObject (M := M) S k, rvClass U = a ∧ rvClass V = b ∧ Isp U V

theorem positiveIsp_class_iff (U V : RVObject (M := M) S k) :
    positiveIsp (rvClass U) (rvClass V) ↔ Isp U V := by
  constructor
  · rintro ⟨A, B, hA, hB, h⟩
    obtain ⟨e⟩ := rvClass_eq_iff_iso.mp hA
    obtain ⟨f⟩ := rvClass_eq_iff_iso.mp hB
    exact h.corollary_6_6 e.symm f.symm
  · intro h
    exact ⟨U, V, rfl, rfl, h⟩

/-- Lemma 6.8 at fixed degree, as an actual additive congruence on the
predecessor's positive Grothendieck quotient. -/
def ispAddCon {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    AddCon (RVKPlus (M := M) S k) where
  r := positiveIsp
  iseqv := by
    constructor
    · intro a
      obtain ⟨U, rfl⟩ := rvClass_surjective a
      exact ⟨U, U, rfl, rfl, Isp.refl U⟩
    · rintro a b ⟨U, V, hU, hV, h⟩
      exact ⟨V, U, hV, hU, h.symm⟩
    · intro a b c hab hbc
      obtain ⟨U, rfl⟩ := rvClass_surjective a
      obtain ⟨V, rfl⟩ := rvClass_surjective b
      obtain ⟨W, rfl⟩ := rvClass_surjective c
      exact (positiveIsp_class_iff U W).mpr
        (((positiveIsp_class_iff U V).mp hab).trans hκ hs hsmall
          ((positiveIsp_class_iff V W).mp hbc))
  add' := by
    rintro a b c d ⟨U, V, rfl, rfl, h⟩ ⟨R, T, rfl, rfl, g⟩
    exact ⟨rvCoprodObject U R, rvCoprodObject V T, rvClass_coprod U R,
      rvClass_coprod V T, h.coprod hκ hs hsmall g⟩

end IntegrationInACVF.Section6
