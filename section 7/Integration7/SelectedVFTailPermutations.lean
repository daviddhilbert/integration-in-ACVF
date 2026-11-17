module

public import IntegrationSection6.VFCoordinateProjections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Extend the original VF order while fixing every added tail coordinate. -/
namespace IntegrationInACVF.Section7
open IntegrationInACVF.Section6

def selectedVFTailPermutation {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (d+n)) :=
  (finCongr (Nat.add_comm d n)).trans ((finAppendEquiv σ d).trans (finCongr (Nat.add_comm n d)))

theorem selected_vf_tail_permutation_original {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    selectedVFTailPermutation d σ (finCongr (Nat.add_comm n d) (Fin.castAdd d i)) =
      finCongr (Nat.add_comm n d) (Fin.castAdd d (σ i)) := by
  simp only [selectedVFTailPermutation,Equiv.trans_apply]
  have hi : finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.castAdd d i)) =
      Fin.castAdd d i := Fin.ext rfl
  rw [hi,finAppendEquiv_left]

theorem selected_vf_tail_permutation_tail {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n)) (j : Fin d) :
    selectedVFTailPermutation d σ (finCongr (Nat.add_comm n d) (Fin.natAdd n j)) =
      finCongr (Nat.add_comm n d) (Fin.natAdd n j) := by
  simp only [selectedVFTailPermutation,Equiv.trans_apply]
  have hj : finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.natAdd n j)) =
      Fin.natAdd n j := Fin.ext rfl
  rw [hj,finAppendEquiv_right]

end IntegrationInACVF.Section7
