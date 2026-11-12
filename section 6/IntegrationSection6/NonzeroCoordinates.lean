import Mathlib.Data.Fintype.EquivFin

/-! Enumerate exactly the nonzero coordinates, retaining any specified
nonzero active coordinate. No algebraic or definability assertion is hidden here. -/

namespace IntegrationInACVF.Section6

open Classical

/-- The selected tuple has successor length because the active coordinate
is nonzero; every omitted coordinate is the absorbing point. -/
theorem exists_nonzero_coordinate_embedding {X : Type*} [Zero X] {n : ℕ}
    (t : Fin n → X) (j : Fin n) (hj : t j ≠ 0) :
    ∃ r : ℕ, ∃ f : Fin (r+1) ↪ Fin n, ∃ l : Fin (r+1),
      f l = j ∧ (∀ i, t (f i) ≠ 0) ∧ (∀ i, i ∉ Set.range f → t i = 0) := by
  classical
  let C := {i : Fin n // t i ≠ 0}
  have hpos : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨⟨j,hj⟩⟩
  let r := Fintype.card C - 1
  have hr : Fintype.card C = r+1 := (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)).symm
  let e : Fin (r+1) ≃ C := (finCongr hr.symm).trans (Fintype.equivFin C).symm
  let f : Fin (r+1) ↪ Fin n := e.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  let l := e.symm ⟨j,hj⟩
  refine ⟨r,f,l,?_,fun i => (e i).property,?_⟩
  · exact congrArg Subtype.val (e.apply_symm_apply ⟨j,hj⟩)
  · intro i hi
    by_contra hnz
    exact hi ⟨e.symm ⟨i,hnz⟩,congrArg Subtype.val (e.apply_symm_apply ⟨i,hnz⟩)⟩

end IntegrationInACVF.Section6
