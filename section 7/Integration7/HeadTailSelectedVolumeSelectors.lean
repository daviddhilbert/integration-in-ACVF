import Integration7.HeadVolumeOrderPermutations
import Integration7.SelectedRVVFTailStandardVolumeCoordinates
import Integration7.HeadTailAppendedVolumeSelectors
import Integration7.StandardPrependHeadSelectors

/-! A single common permutation restores the full selected volume tuple
after contracting a head and then the remaining VF coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ} {A : DefSet (M := M) S (n+1) a}

theorem head_tail_selected_volume_degree (n d : ℕ) : d+n+1 = (1+d)+n := by omega

theorem head_tail_selected_volume_index_rotated
    (σ : Equiv.Perm (Fin (n+1))) (T : HeadPreparation (vfPermutationImage A σ))
    {τ : Equiv.Perm (Fin n)} (D : StandardContraction T.contractedSet τ)
    (ρ : Fin d → Fin a) (ι : Fin (n+1) → Fin D.arity) (hFull : a ≤ D.arity)
    (hHead : ι (σ 0) = suffixIndex D.program.rvArity_le 0)
    (hTail : ∀ j : Fin n, ι (σ j.succ) = D.volumeIndex j)
    (hOld : ∀ δ : Fin a,
      suffixIndex D.program.rvArity_le (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) =
        suffixIndex hFull δ) :
    selectedStandardVolumeIndex D (headVolumeIndex T ρ) ∘
        finCongr (head_tail_selected_volume_degree n d) ∘ headVolumeOrderPermutation d σ =
      Fin.append ι (suffixIndex hFull ∘ ρ) ∘ finCongr (Nat.add_comm d (n+1)) := by
  funext i
  obtain ⟨j,rfl⟩ := (finCongr (Nat.add_comm (n+1) d)).surjective i
  have hcast (j : Fin ((n+1)+d)) :
      finCongr (Nat.add_comm d (n+1)) (finCongr (Nat.add_comm (n+1) d) j) = j := Fin.ext rfl
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · obtain ⟨j,rfl⟩ := σ.surjective i
    cases j using Fin.cases with
    | zero =>
      change Fin.append D.volumeIndex (suffixIndex D.program.rvArity_le ∘ headVolumeIndex T ρ)
          (finCongr (Nat.add_comm (1+d) n) (finCongr (head_tail_selected_volume_degree n d)
            (headVolumeOrderPermutation d σ (finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d (σ 0)))))) =
        Fin.append ι (suffixIndex hFull ∘ ρ) (finCongr _ (finCongr _ (Fin.castAdd d (σ 0))))
      rw [hcast,Fin.append_left,head_volume_order_permutation_head]
      have hi : finCongr (Nat.add_comm (1+d) n) (finCongr (head_tail_selected_volume_degree n d)
          (finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d (Fin.last n)))) =
          Fin.natAdd n (Fin.castAdd d (0 : Fin 1)) := Fin.ext (by simp only [finCongr_apply_coe,Fin.val_castAdd,Fin.val_last,Fin.val_natAdd,Fin.val_zero,Nat.add_zero])
      rw [hi,Fin.append_right]
      exact hHead.symm
    | succ j =>
      change Fin.append D.volumeIndex (suffixIndex D.program.rvArity_le ∘ headVolumeIndex T ρ)
          (finCongr (Nat.add_comm (1+d) n) (finCongr (head_tail_selected_volume_degree n d)
            (headVolumeOrderPermutation d σ (finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d (σ j.succ)))))) =
        Fin.append ι (suffixIndex hFull ∘ ρ) (finCongr _ (finCongr _ (Fin.castAdd d (σ j.succ))))
      rw [hcast,Fin.append_left,head_volume_order_permutation_tail]
      have hi : finCongr (Nat.add_comm (1+d) n) (finCongr (head_tail_selected_volume_degree n d)
          (finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d j.castSucc))) = Fin.castAdd (1+d) j := Fin.ext rfl
      rw [hi,Fin.append_left]
      exact (hTail j).symm
  · change Fin.append D.volumeIndex (suffixIndex D.program.rvArity_le ∘ headVolumeIndex T ρ)
        (finCongr (Nat.add_comm (1+d) n) (finCongr (head_tail_selected_volume_degree n d)
          (headVolumeOrderPermutation d σ (finCongr (Nat.add_comm (n+1) d) (Fin.natAdd (n+1) j))))) =
      Fin.append ι (suffixIndex hFull ∘ ρ) (finCongr _ (finCongr _ (Fin.natAdd (n+1) j)))
    rw [hcast,Fin.append_right,head_volume_order_permutation_old]
    have hi : finCongr (Nat.add_comm (1+d) n) (finCongr (head_tail_selected_volume_degree n d)
        (finCongr (Nat.add_comm (n+1) d) (Fin.natAdd (n+1) j))) = Fin.natAdd n (Fin.natAdd 1 j) := by
      apply Fin.ext
      simp only [finCongr_apply_coe,Fin.val_natAdd]
      omega
    rw [hi,Fin.append_right]
    simpa only [Function.comp_apply,headVolumeIndex,Fin.append_right,headSelectedLabelIndex] using hOld (ρ j)

end IntegrationInACVF.Section7
