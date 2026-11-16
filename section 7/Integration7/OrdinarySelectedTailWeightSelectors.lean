module

public import Integration7.SelectedRVVFTailStandardVolumeCoordinates
public import IntegrationSection6.OrderedSelectedWeights

@[expose] public section

/-! Exact ordinary RV weights of selected contraction coordinates.
These identities retain zero coordinates and require no density form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ} {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem raw_weight_equiv_reindex {k l : ℕ} (e : Fin k ≃ Fin l) (t : Fin l → M) :
    rawWeight (t ∘ e) = rawWeight t := by
  unfold rawWeight
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem standard_ordered_selected_weight (T : StandardContraction A σ) (ρ : Fin d → Fin a)
    (r : Fin T.arity → RV (M := M)) :
    rawWeight (fun j => (r (orderedSelectedIndex T.program ρ j)).val) =
      rawWeight (fun i => (r (T.volumeIndex i)).val) +
        rawWeight (fun j => (r (suffixIndex T.program.rvArity_le (ρ j))).val) := by
  rw [orderedSelectedIndex_weight]
  apply congrArg (fun w => w + rawWeight (fun j => (r (suffixIndex T.program.rvArity_le (ρ j))).val))
  exact (raw_weight_equiv_reindex σ.symm (fun i => (r (T.program.volumeIndex i)).val)).symm

theorem standard_empty_selected_weight (T : StandardContraction A σ) (r : Fin T.arity → RV (M := M)) :
    rawWeight (fun j => (r (orderedSelectedIndex T.program (Fin.elim0 : Fin 0 → Fin a) j)).val) =
      rawWeight (fun i => (r (T.volumeIndex i)).val) := by
  rw [standard_ordered_selected_weight]
  simp only [rawWeight,Finset.univ_eq_empty,Finset.sum_empty,Nat.add_zero]

theorem standard_selected_volume_weight (T : StandardContraction A σ) (ρ : Fin d → Fin a)
    (r : Fin T.arity → RV (M := M)) :
    rawWeight (fun j => (r (selectedStandardVolumeIndex T ρ j)).val) =
      rawWeight (fun j => (r (orderedSelectedIndex T.program ρ j)).val) := by
  let v : Fin (n+d) → M := Fin.append (fun i => (r (T.volumeIndex i)).val)
    (fun j => (r (suffixIndex T.program.rvArity_le (ρ j))).val)
  have h : (fun j => (r (selectedStandardVolumeIndex T ρ j)).val) = v ∘ finCongr (Nat.add_comm d n) := by
    funext j
    unfold selectedStandardVolumeIndex
    dsimp only [Function.comp_apply]
    generalize finCongr (Nat.add_comm d n) j = i
    cases i using Fin.addCases <;> simp only [v,Fin.append_left,Fin.append_right,Function.comp_apply]
  rw [h,raw_weight_equiv_reindex,standard_ordered_selected_weight]
  exact rawWeight_append _ _
end IntegrationInACVF.Section7
