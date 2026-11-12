import Mathlib.GroupTheory.Perm.Fin

/-! Separate the common first coordinate of two contraction orders. -/
namespace IntegrationInACVF.Section6

def headTailPerm {n : ℕ} (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun j => (τ j).succ)
  invFun := Fin.cases 0 (fun j => (τ.symm j).succ)
  left_inv j := by cases j using Fin.cases <;> simp
  right_inv j := by cases j using Fin.cases <;> simp

@[simp] theorem headTailPerm_zero {n : ℕ} (τ : Equiv.Perm (Fin n)) : headTailPerm τ 0 = 0 := rfl
@[simp] theorem headTailPerm_succ {n : ℕ} (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    headTailPerm τ j.succ = (τ j).succ := rfl

theorem headTailPerm_symm {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (headTailPerm τ).symm = headTailPerm τ.symm := rfl

theorem exists_headTailPerm_of_zero {n : ℕ} (π : Equiv.Perm (Fin (n+1))) (h0 : π 0 = 0) :
    ∃ τ : Equiv.Perm (Fin n), π = headTailPerm τ := by
  have hne (j : Fin n) : π j.succ ≠ 0 := by
    intro h
    have he := π.injective (h.trans h0.symm)
    exact Fin.succ_ne_zero j he
  have h0' : π.symm 0 = 0 := π.injective ((π.apply_symm_apply 0).trans h0.symm)
  have hne' (j : Fin n) : π.symm j.succ ≠ 0 := by
    intro h
    have he := π.symm.injective (h.trans h0'.symm)
    exact Fin.succ_ne_zero j he
  let τ : Equiv.Perm (Fin n) := {
    toFun := fun j => (π j.succ).pred (hne j)
    invFun := fun j => (π.symm j.succ).pred (hne' j)
    left_inv := by
      intro j
      simp only [Fin.succ_pred,Equiv.symm_apply_apply,Fin.pred_succ]
    right_inv := by
      intro j
      simp only [Fin.succ_pred,Equiv.apply_symm_apply,Fin.pred_succ] }
  refine ⟨τ,Equiv.ext fun j => ?_⟩
  cases j using Fin.cases with
  | zero => exact h0
  | succ j => exact (Fin.succ_pred (π j.succ) (hne j)).symm

theorem contractionOrders_common_head {n : ℕ} (σ υ : Equiv.Perm (Fin (n+1))) (h0 : σ 0 = υ 0) :
    ∃ τ : Equiv.Perm (Fin n), υ = (headTailPerm τ).trans σ := by
  obtain ⟨τ,hτ⟩ := exists_headTailPerm_of_zero (υ.trans σ.symm) (by
    change σ.symm (υ 0) = 0
    rw [← h0,Equiv.symm_apply_apply])
  refine ⟨τ,Equiv.ext fun j => ?_⟩
  have h := congrArg σ (congrArg (fun e : Equiv.Perm (Fin (n+1)) => e j) hτ)
  exact (σ.apply_symm_apply (υ j)).symm.trans h

end IntegrationInACVF.Section6
