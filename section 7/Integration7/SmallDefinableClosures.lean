module

public import Section3.ClosureConventions
public import Section4.SmallGeneratedBase
public import Mathlib.ModelTheory.Encoding

@[expose] public section

/-! Closing a small real parameter set under definability preserves
smallness below an uncountable cardinal. Singleton-defining formulas
encode its elements injectively in the actual countable LRV language. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem small_definable_closure {κ : Cardinal} (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 < κ) (S : Set M) (hS : Cardinal.mk S < κ) :
    Cardinal.mk (definableClosure S) < κ := by
  have hFormula (a : definableClosure S) :
      ∃ φ : LRV.Formula (S ⊕ Fin 1), {x : Fin 1 → M | x 0 ∈ ({a.val} : Set M)} =
        {v | φ.Realize (Sum.elim Subtype.val v)} :=
    Set.definable_iff_exists_formula_sum.mp ((mem_definableClosure_iff_raw hc S a.val).mp a.property)
  choose φ hφ using hFormula
  have hInj : Function.Injective φ := by
    intro a b he
    have ha : (φ a).Realize (Sum.elim Subtype.val (fun _ : Fin 1 => a.val)) :=
      (Set.ext_iff.mp (hφ a) (fun _ => a.val)).mp (Set.mem_singleton a.val)
    rw [he] at ha
    exact Subtype.ext ((Set.ext_iff.mp (hφ b) (fun _ => a.val)).mpr ha)
  have hCode : Cardinal.mk (definableClosure S) ≤ Cardinal.mk (LRV.Formula (S ⊕ Fin 1)) :=
    Cardinal.mk_le_of_injective hInj
  have hZero : Cardinal.mk (LRV.Formula (S ⊕ Fin 1)) ≤
      Cardinal.mk (Σ n, LRV.BoundedFormula (S ⊕ Fin 1) n) :=
    Cardinal.mk_le_of_injective (show Function.Injective
      (fun p : LRV.Formula (S ⊕ Fin 1) => (⟨0,p⟩ : Σ n, LRV.BoundedFormula (S ⊕ Fin 1) n)) from
        by intro p q h;cases h;rfl)
  have hLang : LRV.card < κ := (show LRV.card ≤ Cardinal.aleph0 from Cardinal.mk_le_aleph0).trans_lt hκ
  have hOne : Cardinal.mk (Fin 1) < κ := by
    rw [Cardinal.mk_fintype,Fintype.card_fin]
    exact Cardinal.one_lt_aleph0.trans hκ
  have hSum : Cardinal.mk (S ⊕ Fin 1) < κ := by
    simp only [Cardinal.mk_sum,Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hκ.le hS hOne
  have hBound : Cardinal.mk (Σ n, LRV.BoundedFormula (S ⊕ Fin 1) n) ≤
      max Cardinal.aleph0 (Cardinal.mk (S ⊕ Fin 1)+LRV.card) := by
    simpa only [Cardinal.lift_id] using (BoundedFormula.card_le (L := LRV) (α := S ⊕ Fin 1))
  exact (hCode.trans (hZero.trans hBound)).trans_lt (max_lt hκ (Cardinal.add_lt_of_lt hκ.le hSum hLang))

end IntegrationInACVF.Section7
