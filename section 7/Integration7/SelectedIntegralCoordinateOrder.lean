module

public import Integration7.SelectedStandardVolumeObjects

@[expose] public section

/-! The fixed coordinate permutation from selected-first appended
contractions to VF-first selected contractions in the identity VF order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a k : ℕ}

def appendedToOriginalVolumePermutation (n k : ℕ) : Equiv.Perm (Fin (appendVolumeDegree n k+1)) :=
  (finCongr ((append_volume_length_eq n k).trans (Nat.add_comm (k+1) n))).trans
    ((finAddFlip : Fin (n+(k+1)) ≃ Fin ((k+1)+n)).trans
      (finCongr (append_volume_length_eq n k)).symm)

theorem identity_selected_volume_index_from_append
    {A : DefSet (M := M) S n a} (T : StandardContraction A (Equiv.refl _))
    (ρ : Fin (k+1) → Fin a) :
    selectedStandardVolumeIndex T ρ ∘ finCongr (append_volume_length_eq n k) =
      orderedAppendVolumeIndex T.program ρ ∘ appendedToOriginalVolumePermutation n k := by
  funext i
  let z : Fin (n+(k+1)) := finCongr ((append_volume_length_eq n k).trans (Nat.add_comm (k+1) n)) i
  have hz : finCongr (Nat.add_comm (k+1) n) (finCongr (append_volume_length_eq n k) i) = z := Fin.ext rfl
  have hClosed := congrFun (ordered_append_volume_index_closed T.program ρ)
    ((finAddFlip : Fin (n+(k+1)) ≃ Fin ((k+1)+n)) z)
  change Fin.append T.volumeIndex (suffixIndex T.program.rvArity_le ∘ ρ)
      (finCongr (Nat.add_comm (k+1) n) (finCongr (append_volume_length_eq n k) i)) = _
  rw [hz]
  change Fin.append T.program.volumeIndex (suffixIndex T.program.rvArity_le ∘ ρ) z = _
  calc
    _ = Fin.append (suffixIndex T.program.rvArity_le ∘ ρ) T.program.volumeIndex
        ((finAddFlip : Fin (n+(k+1)) ≃ Fin ((k+1)+n)) z) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) z
      · simp only [Fin.append_left,finAddFlip_apply_castAdd,Fin.append_right]
      · simp only [Fin.append_right,finAddFlip_apply_natAdd,Fin.append_left]
    _ = _ := hClosed.symm

end IntegrationInACVF.Section7
