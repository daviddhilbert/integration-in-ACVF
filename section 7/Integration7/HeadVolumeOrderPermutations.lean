import Integration7.SelectedVFTailPermutations
import IntegrationSection6.HeadTailPermutations

/-! The common volume-coordinate permutation from a contracted tail's
tuple (tail, head, old RV) to the original VF order and old RV tuple. -/
namespace IntegrationInACVF.Section7

def headVolumeOrderPermutation {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    Equiv.Perm (Fin (d+n+1)) :=
  selectedVFTailPermutation d (σ.symm.trans (finRotate (n+1)).symm)

theorem head_volume_order_permutation_head {n : ℕ} (d : ℕ)
    (σ : Equiv.Perm (Fin (n+1))) :
    headVolumeOrderPermutation d σ (finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d (σ 0))) =
      finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d (Fin.last n)) := by
  rw [headVolumeOrderPermutation,selected_vf_tail_permutation_original]
  change finCongr _ (Fin.castAdd d ((finRotate (n+1)).symm (σ.symm (σ 0)))) = _
  rw [σ.symm_apply_apply]
  have hz : (finRotate (n+1)).symm 0 = Fin.last n := by
    apply (finRotate (n+1)).injective
    rw [Equiv.apply_symm_apply]
    exact (finRotate_last' (n := n)).symm
  rw [hz]

theorem head_volume_order_permutation_tail {n : ℕ} (d : ℕ)
    (σ : Equiv.Perm (Fin (n+1))) (j : Fin n) :
    headVolumeOrderPermutation d σ (finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d (σ j.succ))) =
      finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d j.castSucc) := by
  rw [headVolumeOrderPermutation,selected_vf_tail_permutation_original]
  change finCongr _ (Fin.castAdd d ((finRotate (n+1)).symm (σ.symm (σ j.succ)))) = _
  rw [σ.symm_apply_apply]
  have hj : (finRotate (n+1)).symm j.succ = j.castSucc := by
    apply (finRotate (n+1)).injective
    rw [Equiv.apply_symm_apply]
    exact (finRotate_of_lt j.isLt).symm
  rw [hj]

theorem head_volume_order_permutation_old {n : ℕ} (d : ℕ)
    (σ : Equiv.Perm (Fin (n+1))) (j : Fin d) :
    headVolumeOrderPermutation d σ (finCongr (Nat.add_comm (n+1) d) (Fin.natAdd (n+1) j)) =
      finCongr (Nat.add_comm (n+1) d) (Fin.natAdd (n+1) j) :=
  selected_vf_tail_permutation_tail d _ j

end IntegrationInACVF.Section7
