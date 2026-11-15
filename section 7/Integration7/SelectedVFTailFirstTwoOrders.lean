import Integration7.SelectedVFTailPermutations

/-! Extending the VF order fixes the added tail and retains exactly
the first-two exchange hypotheses of Lemma 7.7. -/
namespace IntegrationInACVF.Section7

theorem selected_vf_tail_first_two_orders {n d : ℕ}
    (σ υ : Equiv.Perm (Fin (n+2)))
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ) :
    selectedVFTailPermutation d υ 0 = selectedVFTailPermutation d σ (0 : Fin (d+n+1)).succ ∧
    selectedVFTailPermutation d υ (0 : Fin (d+n+1)).succ = selectedVFTailPermutation d σ 0 ∧
    ∀ j : Fin (d+n), selectedVFTailPermutation d υ j.succ.succ =
      selectedVFTailPermutation d σ j.succ.succ := by
  have hz : (0 : Fin (d+(n+2))) = finCongr (Nat.add_comm (n+2) d) (Fin.castAdd d (0 : Fin (n+2))) := Fin.ext rfl
  have ho : ((0 : Fin (d+n+1)).succ : Fin (d+(n+2))) =
      finCongr (Nat.add_comm (n+2) d) (Fin.castAdd d ((0 : Fin (n+1)).succ)) := Fin.ext rfl
  refine ⟨?_,?_,?_⟩
  · rw [hz,ho,selected_vf_tail_permutation_original,selected_vf_tail_permutation_original,h0]
  · rw [hz,ho,selected_vf_tail_permutation_original,selected_vf_tail_permutation_original,h1]
  · intro j
    by_cases hj : j.val < n
    · let i : Fin n := ⟨j.val,hj⟩
      have he : (j.succ.succ : Fin (d+(n+2))) =
          finCongr (Nat.add_comm (n+2) d) (Fin.castAdd d i.succ.succ) := Fin.ext rfl
      rw [he,selected_vf_tail_permutation_original,selected_vf_tail_permutation_original,hTail]
    · let i : Fin d := ⟨j.val-n,by have h := j.isLt; omega⟩
      have he : (j.succ.succ : Fin (d+(n+2))) =
          finCongr (Nat.add_comm (n+2) d) (Fin.natAdd (n+2) i) := by
        apply Fin.ext
        simp only [Fin.val_succ,finCongr_apply_coe,Fin.val_natAdd,i]
        omega
      rw [he,selected_vf_tail_permutation_tail,selected_vf_tail_permutation_tail]

end IntegrationInACVF.Section7
