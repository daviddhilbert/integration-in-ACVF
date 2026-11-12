import IntegrationSection6.FiniteGammaWeightedIsos
import Section4.RVLabelCompression

/-! RV weight balance is a real definable condition on the complete
volume tuples, including absorbing zero. This supplies the numerical
condition in finite isomorphism witness validity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M]

theorem rawWeight_fibre_raw_definable (S : Set M) (k N : ℕ) :
    S.Definable LRV {t : Fin k → M | rawWeight t = N} := by
  induction k generalizing N with
  | zero =>
    by_cases hN : N = 0
    · simpa [rawWeight,hN] using (Set.definable_univ (L := LRV) (A := S) (α := Fin 0))
    · have he : {t : Fin 0 → M | rawWeight t = N} = ∅ := by
        apply Set.ext
        intro t
        simp [rawWeight,Ne.symm hN]
      rw [he]
      exact Set.definable_empty
  | succ k ih =>
    have hz := rvZero_coordinate_definable S (Fin.last k)
    have hWeight (t : Fin (k+1) → M) :
        rawWeight t = rawWeight (t ∘ Fin.castSucc) + (if t (Fin.last k) ≠ iRVZero then 1 else 0) := by
      unfold rawWeight
      rw [Fin.sum_univ_castSucc]
      rfl
    cases N with
    | zero =>
      have h := ((ih 0).preimage_comp Fin.castSucc).inter hz
      convert h using 1
      apply Set.ext
      intro t
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage]
      rw [hWeight]
      by_cases ht : t (Fin.last k) = iRVZero <;> simp [ht]
    | succ N =>
      have h := (((ih (N+1)).preimage_comp Fin.castSucc).inter hz).union
        (((ih N).preimage_comp Fin.castSucc).inter hz.compl)
      convert h using 1
      apply Set.ext
      intro t
      simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_preimage,Set.mem_compl_iff]
      rw [hWeight]
      by_cases ht : t (Fin.last k) = iRVZero <;> simp [ht]

variable [hM : M ⊨ Axioms.ACVF]
local notation "NStr" => (@CanonicalStructure.normalize M sM)

theorem rawWeight_fibre_definable (S : Set M) (k N : ℕ) :
    @Set.Definable M S LRV NStr (Fin k) {t | @rawWeight M sM k t = N} := by
  have h := @rawWeight_fibre_raw_definable M NStr S k N
  have hz : @iRVZero M NStr = @iRVZero M sM := @CanonicalStructure.sortZero_normalize M sM .rv
  convert h using 1
  apply Set.ext
  intro t
  simp only [Set.mem_ofPred_eq,rawWeight,hz]

theorem rawWeight_balance_definable (S : Set M) (k : ℕ) :
    DefinableOver S (fun _ : Fin (k+k) => .rv)
      {t | (∀ j, iRV (t j)) ∧ rawWeight (t ∘ Fin.castAdd k) = rawWeight (t ∘ Fin.natAdd k)} := by
  let C (i : Fin (k+1)) : Set (Fin (k+k) → M) :=
    {t | rawWeight (t ∘ Fin.castAdd k) = i.val ∧ rawWeight (t ∘ Fin.natAdd k) = i.val}
  have hC (i : Fin (k+1)) : @Set.Definable M S LRV NStr (Fin (k+k)) (C i) := by
    have hl := @Set.Definable.preimage_comp M S LRV NStr (Fin k) (Fin (k+k)) (Fin.castAdd k) _
      (rawWeight_fibre_definable S k i.val)
    have hr := @Set.Definable.preimage_comp M S LRV NStr (Fin k) (Fin (k+k)) (Fin.natAdd k) _
      (rawWeight_fibre_definable S k i.val)
    letI := NStr
    exact hl.inter hr
  have hEq : @Set.Definable M S LRV NStr (Fin (k+k))
      {t | rawWeight (t ∘ Fin.castAdd k) = rawWeight (t ∘ Fin.natAdd k)} := by
    letI := NStr
    have h := Set.definable_iUnion_of_finite hC
    convert h using 1
    apply Set.ext
    intro t
    constructor
    · intro he
      refine Set.mem_iUnion.mpr ⟨⟨@rawWeight M sM k (t ∘ Fin.castAdd k),?_⟩,rfl,he.symm⟩
      exact Nat.lt_succ_of_le (@rawWeight_le_arity M sM hM k (t ∘ Fin.castAdd k))
    · intro ht
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
      exact hi.1.trans hi.2.symm
  have hSort := ((definableOver_iff_normalized_raw S (fun _ : Fin (k+k) => .rv) _).mp
    (sortedUniverse_definable S (fun _ : Fin (k+k) => .rv))).1
  apply (definableOver_iff_normalized_raw S (fun _ : Fin (k+k) => .rv) _).mpr
  letI := NStr
  exact ⟨hSort.inter hEq,fun _ h => h.1⟩

end IntegrationInACVF.Section6
