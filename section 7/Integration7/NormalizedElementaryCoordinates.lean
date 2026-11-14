import Integration7.ElementaryBlowupConstruction
import IntegrationSection6.GammaElementaryStructure

/-! Normalization preserves the actual cone predicate and elementary
coordinate program on typed RV tuples, including the absorbing zero. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem positiveRV_normalize (S : Set M) (t : Fin 1 → CanonicalRV.RVSort M) :
    t ∈ @DefSet.carrier LRV M N _ S (@Section6.positiveRV M N S) ↔
      t ∈ (Section6.positiveRV S).carrier := by
  have hOne := @CanonicalStructure.normalize_fun M sM 0 Fn.rvOne Fin.elim0 (fun j => j.elim0)
  change @iRVOne M N = @iRVOne M sM at hOne
  change (¬ @iLe M N (t 0).val (@iRVOne M N)) ↔ (¬ iLe (t 0).val iRVOne)
  rw [hOne]
  apply not_congr
  exact @CanonicalStructure.normalize_rel M sM 2 Rel.rvLe ![(t 0).val,iRVOne]
    (fun i => by fin_cases i; exact (t 0).property; rw [← RVOperations.one_val]; exact (1 : CanonicalRV.RVSort M).property)

theorem blowupValue_normalize (i : Fin n) (t : Fin n → CanonicalRV.RVSort M) (s : CanonicalRV.RVSort M) :
    @Section6.blowupValue M N hN n i t s = Section6.blowupValue i t s := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Section6.blowupValue,ite_true]
    apply Subtype.ext
    rw [@RVOperations.mul_val M N hN,@RVOperations.mul_val M sM hM]
    exact @CanonicalStructure.normalize_fun M sM 2 Fn.rvMul ![s.val,(t i).val]
      (fun q => by fin_cases q; exact s.property; exact (t i).property)
  · simp only [Section6.blowupValue,hj,ite_false]

theorem oldVolumeParameterBlowupMap_normalize (S T : Set M) (i : Fin n)
    (w : Fin (n+1) → CanonicalRV.RVSort M) :
    (@Section6.oldVolumeParameterBlowupMap M N hN n S i ⟨w,Set.mem_univ _⟩).val =
      (Section6.oldVolumeParameterBlowupMap T i ⟨w,Set.mem_univ _⟩).val := by
  change @Section6.blowupValue M N hN n i (w ∘ Fin.castAdd 1) (w (Fin.natAdd n 0)) =
    Section6.blowupValue i (w ∘ Fin.castAdd 1) (w (Fin.natAdd n 0))
  exact blowupValue_normalize i _ _

end IntegrationInACVF.Section7
