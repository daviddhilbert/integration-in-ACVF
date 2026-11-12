import Section4.RVTupleFibres
import Section3.SortedBoolean

/-! RV tuple fibres are definable in the original sorted structure, even
when its arbitrary off-sort totalization is not canonical. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M]

theorem tupleRVFibre_normalize {n : ℕ} (t : Fin n → M) :
    @tupleRVFibre M (@CanonicalStructure.normalize M sM) n t = tupleRVFibre t := by
  ext a
  apply forall_congr'
  intro i
  change (iVF (a i) ∧ @iRv M (@CanonicalStructure.normalize M sM) (a i) = t i) ↔
    (iVF (a i) ∧ iRv (a i) = t i)
  apply and_congr_right
  intro ha
  have he := @CanonicalStructure.normalize_fun M sM 1 Fn.rvMap ![a i]
    (by intro j; fin_cases j; exact ha)
  change @iRv M (@CanonicalStructure.normalize M sM) (a i) = iRv (a i) at he
  rw [he]

variable [hM : M ⊨ Axioms.ACVF]

theorem actualRVFibre_definable (S : Set M) {n : ℕ}
    (t : Fin n → CanonicalRV.RVSort M) :
    DefinableOver (S ∪ Set.range (rvValues t)) (fun _ => .vf) (tupleRVFibre (rvValues t)) := by
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  let hN := @CanonicalStructure.normalized_model M sM hM
  apply (@definableOver_iff_normalized_raw M sM hM (S ∪ Set.range (rvValues t)) n
    (fun _ => .vf) (tupleRVFibre (rvValues t))).mpr
  refine ⟨?_,fun a ha i => (ha i).1⟩
  have hr := @rvTupleFibre_raw_definable M N hN S n t
  have hF : @tupleRVFibre M N n (rvValues t) = @tupleRVFibre M sM n (rvValues t) :=
    @tupleRVFibre_normalize M sM n (rvValues t)
  exact Eq.mp (congrArg (fun C => @Set.Definable M
    (S ∪ Set.range (rvValues t)) LRV N (Fin n) C) hF) hr

end IntegrationInACVF.Section6
