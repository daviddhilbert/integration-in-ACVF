import Section3.TupleCompactness

/-! Finite-tuple definable compactness from the predecessor's genuine
saturation interface. The tuple arity is arbitrary; no geometric
compactness assertion is included in the assumptions. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.DefinableTupleCompactness

variable {M : Type} [LRV.Structure M] {n : ℕ}

theorem realize_fip {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (C : Set (Set (Fin n → M)))
    (hC : ∀ D ∈ C, S.Definable LRV D)
    (hFIP : ∀ (ι : Type) [Finite ι] (D : ι → C), ∃ x, ∀ i, x ∈ (D i).val) :
    ∃ x, ∀ D ∈ C, x ∈ D := by
  have hformula (D : C) := raw_definable_formula_tuple (hC D.val D.property)
  let φ : C → LRV.BoundedFormula S n := fun D => Classical.choose (hformula D)
  have hφ (D : C) (x : Fin n → M) : (φ D).Realize Subtype.val x ↔ x ∈ D.val :=
    Classical.choose_spec (hformula D) x
  have hp : FinitelySatisfiable (Subtype.val : S → M) (Set.range φ) := by
    intro l hl
    have hchoice (i : Fin l.length) : ∃ D : C, φ D = l.get i :=
      hl (l.get i) (List.get_mem l i)
    choose D hD using hchoice
    obtain ⟨x,hx⟩ := hFIP (Fin l.length) D
    refine ⟨x,?_⟩
    intro ψ hψ
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hψ
    rw [← hD i]
    exact (hφ (D i) x).mpr (hx i)
  obtain ⟨x,hx⟩ := hs S Subtype.val hsmall (Set.range φ) hp
  exact ⟨x,fun D hD => (hφ ⟨D,hD⟩ x).mp (hx _ ⟨⟨D,hD⟩,rfl⟩)⟩

theorem finite_inconsistent {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (C : Set (Set (Fin n → M)))
    (hC : ∀ D ∈ C, S.Definable LRV D)
    (hbad : ¬ ∃ x, ∀ D ∈ C, x ∈ D) :
    ∃ F : Finset (Set (Fin n → M)), (∀ D ∈ F, D ∈ C) ∧
      ¬ ∃ x, ∀ D ∈ F, x ∈ D := by
  classical
  by_contra hn
  apply hbad
  apply realize_fip hs S hsmall C hC
  intro ι _ D
  let F := (Set.finite_range (fun i => (D i).val)).toFinset
  have hFC : ∀ U ∈ F, U ∈ C := by
    intro U hU
    obtain ⟨i,rfl⟩ := (Set.finite_range (fun i => (D i).val)).mem_toFinset.mp hU
    exact (D i).property
  have hne : ∃ x, ∀ U ∈ F, x ∈ U := by
    by_contra he
    exact hn ⟨F,hFC,he⟩
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,fun i => hx _ ((Set.finite_range (fun i => (D i).val)).mem_toFinset.mpr ⟨i,rfl⟩)⟩

end IntegrationInACVF.Section3ACVF.DefinableTupleCompactness
