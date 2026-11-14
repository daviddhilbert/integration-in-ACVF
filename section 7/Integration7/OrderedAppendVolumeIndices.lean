import Integration7.OrderedAppendVolumeContractions

/-! The recursive selected tuple is exactly the original selected labels
followed by every contracted VF tag in the program's order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a l k : ℕ}
variable {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}

theorem append_volume_length_eq (n k : ℕ) : appendVolumeDegree n k+1 = (k+1)+n := by
  rw [append_volume_degree_eq]
  omega

theorem ordered_append_old_index
    (T : OrderedContractionProgram S U V) (ρ : Fin (k+1) → Fin a) (i : Fin (k+1)) :
    orderedAppendVolumeIndex T ρ (Fin.cast (append_volume_length_eq n k).symm (Fin.castAdd n i)) =
      suffixIndex T.rvArity_le (ρ i) := by
  induction T generalizing k with
  | zero U =>
    have hi : Fin.cast (append_volume_length_eq 0 k).symm (Fin.castAdd 0 i) = i := Fin.ext rfl
    change ρ _ = _
    rw [hi]
    apply Fin.ext
    simp [suffixIndex]
  | @step n a l U V T tail ih =>
    have hi : Fin.cast (append_volume_length_eq (n+1) k).symm (Fin.castAdd (n+1) i) =
        Fin.cast (append_volume_length_eq n (k+1)).symm (Fin.castAdd n (Fin.castAdd 1 i)) := Fin.ext rfl
    change orderedAppendVolumeIndex tail (headAppendVolumeIndex T ρ) _ = _
    rw [hi,ih]
    simp only [headAppendVolumeIndex,Fin.append_left]
    apply Fin.ext
    have hT := specialRelative_rvArity_le T.special
    have ht := tail.rvArity_le
    change l-(1+T.arity)+(1+(T.arity-a+(ρ i).val)) = l-a+(ρ i).val
    omega

theorem ordered_append_vf_index
    (T : OrderedContractionProgram S U V) (ρ : Fin (k+1) → Fin a) (i : Fin n) :
    orderedAppendVolumeIndex T ρ (Fin.cast (append_volume_length_eq n k).symm (Fin.natAdd (k+1) i)) =
      T.volumeIndex i := by
  induction T generalizing k with
  | zero U => exact Fin.elim0 i
  | @step n a l U V T tail ih =>
    cases i using Fin.cases with
    | zero =>
      have hi : Fin.cast (append_volume_length_eq (n+1) k).symm (Fin.natAdd (k+1) (0 : Fin (n+1))) =
          Fin.cast (append_volume_length_eq n (k+1)).symm
            (Fin.castAdd n (Fin.natAdd (k+1) (0 : Fin 1))) := Fin.ext rfl
      change orderedAppendVolumeIndex tail (headAppendVolumeIndex T ρ) _ = _
      rw [hi,ordered_append_old_index]
      simp only [headAppendVolumeIndex,Fin.append_right,OrderedContractionProgram.volumeIndex,Fin.cases_zero]
      rfl
    | succ i =>
      have hi : Fin.cast (append_volume_length_eq (n+1) k).symm (Fin.natAdd (k+1) i.succ) =
          Fin.cast (append_volume_length_eq n (k+1)).symm (Fin.natAdd ((k+1)+1) i) := by
        apply Fin.ext
        simp only [Fin.coe_cast,Fin.val_natAdd,Fin.val_succ]
        omega
      change orderedAppendVolumeIndex tail (headAppendVolumeIndex T ρ) _ = _
      rw [hi,ih]
      rfl

private theorem finCongr_symm_cast {c d : ℕ} (h : c=d) (i : Fin d) :
    (finCongr h).symm i = Fin.cast h.symm i := by
  subst d
  rfl

theorem ordered_append_volume_index_closed
    (T : OrderedContractionProgram S U V) (ρ : Fin (k+1) → Fin a) :
    orderedAppendVolumeIndex T ρ ∘ (finCongr (append_volume_length_eq n k)).symm =
      Fin.append (fun j => suffixIndex T.rvArity_le (ρ j)) T.volumeIndex := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Function.comp_apply,finCongr_symm_cast,Fin.append_left] using ordered_append_old_index T ρ j
  · simpa only [Function.comp_apply,finCongr_symm_cast,Fin.append_right] using ordered_append_vf_index T ρ j

theorem ordered_append_density_index
    (T : OrderedContractionProgram S U V) (δ : Fin a) :
    orderedAppendDensityIndex T δ = suffixIndex T.rvArity_le δ := by
  induction T with
  | zero U => apply Fin.ext; simp [orderedAppendDensityIndex,suffixIndex]
  | @step n a l U V T tail ih =>
    change orderedAppendDensityIndex tail _ = _
    rw [ih]
    apply Fin.ext
    have hT := specialRelative_rvArity_le T.special
    have ht := tail.rvArity_le
    change l-(1+T.arity)+(1+(T.arity-a+δ.val)) = l-a+δ.val
    omega

end IntegrationInACVF.Section7
