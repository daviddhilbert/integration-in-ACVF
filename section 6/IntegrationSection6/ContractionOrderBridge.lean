import IntegrationSection6.HeadTailPermutations

/-! Put two distinct first coordinates in the first two positions. -/
namespace IntegrationInACVF.Section6

theorem exists_contraction_bridge_order {n : ℕ} (σ υ : Equiv.Perm (Fin (n+2)))
    (hne : σ 0 ≠ υ 0) :
    ∃ π : Equiv.Perm (Fin (n+2)), π 0 = σ 0 ∧ π (0 : Fin (n+1)).succ = υ 0 := by
  let j := σ.symm (υ 0)
  have hj : j ≠ 0 := by
    intro h
    have he : υ 0 = σ 0 := (σ.apply_symm_apply (υ 0)).symm.trans (congrArg σ h)
    exact hne he.symm
  let π := (Equiv.swap (0 : Fin (n+1)).succ j).trans σ
  refine ⟨π,?_,?_⟩
  · change σ (Equiv.swap (0 : Fin (n+1)).succ j 0) = σ 0
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm hj.symm]
  · change σ (Equiv.swap (0 : Fin (n+1)).succ j (0 : Fin (n+1)).succ) = υ 0
    rw [Equiv.swap_apply_left]
    exact σ.apply_symm_apply _

end IntegrationInACVF.Section6
