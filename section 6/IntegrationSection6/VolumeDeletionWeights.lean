import IntegrationSection6.ElementaryIsomorphism
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvWeight_delete_nonzero (t : Fin (n+1) → CanonicalRV.RVSort M) (i : Fin (n+1))
    (hi : (t i).val ≠ iRVZero) :
    @rvWeight M sM (n+1) t = @rvWeight M sM n (fun j => t (i.succAbove j)) + 1 := by
  unfold rvWeight
  rw [Fin.sum_univ_succAbove _ i]
  rw [if_pos hi]
  exact Nat.add_comm _ _

theorem rvWeight_one_tuple : rvWeight (fun _ : Fin 1 => (1 : CanonicalRV.RVSort M)) = 1 := by
  simp only [rvWeight,Fin.sum_univ_one,RVOperations.one_val,ne_eq,RVCalc.rv_one_ne_zero hM,
    not_false_eq_true,ite_true]

theorem rvWeight_singleton_balance (s : CanonicalRV.RVSort M) :
    @rvWeight M sM 1 (fun _ : Fin 1 => s) + (if s = 0 then 1 else 0) = 1 := by
  unfold rvWeight
  rw [Fin.sum_univ_one]
  by_cases hs : s = 0
  · simp [hs,RVOperations.zero_val]
  · have hc : s.val ≠ @iRVZero M sM := by
      intro he
      apply hs
      apply Subtype.ext
      exact he.trans RVOperations.zero_val.symm
    rw [ite_eq_left hc]
    simp only [hs,ite_false,Nat.add_zero]

theorem blowupValue_weight_deleted (t : Fin (n+1) → CanonicalRV.RVSort M) (i : Fin (n+1))
    (s : CanonicalRV.RVSort M) (hi : (t i).val ≠ iRVZero) :
    @rvWeight M sM (n+1) (@blowupValue M sM hM (n+1) i t s) =
      @rvWeight M sM n (fun j => t (i.succAbove j)) + @rvWeight M sM 1 (fun _ : Fin 1 => s) := by
  have h := @blowupValue_weight_balance M sM hM (n+1) i t s hi
  have hd := rvWeight_delete_nonzero t i hi
  have hs := rvWeight_singleton_balance s
  omega

end IntegrationInACVF.Section6
