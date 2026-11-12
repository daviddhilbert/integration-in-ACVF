import IntegrationSection6.GammaLabelSliceValidity
import Section4.RVLabelCompression

/-! Real sorted coordinate conditions used in admissibility validity.
Normalization preserves the single absorbing RV zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "NStr" => (@CanonicalStructure.normalize M sM)

theorem sorted_coordinate_nonzero_definable (S : Set M) {n : ℕ} (sn : Fin n → SortTag) (i : Fin n) :
    DefinableOver S sn {w | w ∈ sortedUniverse sn ∧ w i ≠ iRVZero} := by
  have hz : @iRVZero M NStr = @iRVZero M sM := @CanonicalStructure.sortZero_normalize M sM .rv
  have hZ : @Set.Definable M S LRV NStr (Fin n) {w | w i = @iRVZero M sM} := by
    have h := @rvZero_coordinate_definable M NStr S (Fin n) i
    simpa only [hz] using h
  have hSort := ((definableOver_iff_normalized_raw S sn _).mp (sortedUniverse_definable S sn)).1
  apply (definableOver_iff_normalized_raw S sn _).mpr
  letI := NStr
  exact ⟨hSort.inter hZ.compl,fun _ h => h.1⟩

theorem sorted_coordinates_except_eq_definable (S : Set M) {n k : ℕ}
    (sn : Fin n → SortTag) (i : Fin k) (left right : Fin k → Fin n) :
    DefinableOver S sn {w | w ∈ sortedUniverse sn ∧ ∀ j, j ≠ i → w (left j) = w (right j)} := by
  have hEq : @Set.Definable M S LRV NStr (Fin n)
      {w | ∀ j, j ≠ i → w (left j) = w (right j)} := by
    have hj (j : Fin k) : @Set.Definable M S LRV NStr (Fin n)
        {w | j ≠ i → w (left j) = w (right j)} := by
      letI := NStr
      by_cases hji : j = i
      · simp only [hji,ne_eq,not_true_eq_false,false_implies]
        exact Set.definable_univ
      · simpa only [hji,Ne,not_false_eq_true,true_implies] using
          (@Set.DefinableFun.ofPred_eq M LRV NStr (Fin n) S _ _
            (@Set.DefinableFun.proj M LRV NStr _ S (left j))
            (@Set.DefinableFun.proj M LRV NStr _ S (right j)))
    letI := NStr
    convert Set.definable_iInter_of_finite hj using 1
    apply Set.ext
    intro w
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
  have hSort := ((definableOver_iff_normalized_raw S sn _).mp (sortedUniverse_definable S sn)).1
  apply (definableOver_iff_normalized_raw S sn _).mpr
  letI := NStr
  exact ⟨hSort.inter hEq,fun _ h => h.1⟩

end IntegrationInACVF.Section6
