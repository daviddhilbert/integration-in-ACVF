import IntegrationSection3ACVF.NormalizedBallParameters

/-! A genuinely nontrivial original Gamma value supplies one in the
normalized model, via the same RV code and the actual strict preorder. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.NormalizedNontrivialValue

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => @CanonicalStructure.normalize M sM
local notation "hN" => @CanonicalStructure.normalized_model M sM hM

theorem exists_gt_one (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ β : @Values.Gamma M N hN, 1 < β := by
  letI : @FirstOrder.Language.Theory.Model LRV M N Axioms.ACVF := hN
  obtain ⟨t,ht0,htδ⟩ := Values.gamma_has_nonzero_representative δ
  have hz : @iRVZero M N = @iRVZero M sM := CanonicalStructure.sortZero_normalize .rv
  let tN : @CanonicalRV.RVSort M N := ⟨t.val,t.property⟩
  have htN : tN.val ≠ @iRVZero M N := by simpa only [hz] using ht0
  let β : @Values.Gamma M N hN := @Values.gammaOf M N hN tN htN
  let u : CanonicalRV.RVSort M := 1
  let uN : @CanonicalRV.RVSort M N := ⟨u.val,u.property⟩
  have hOne : @iRVOne M N = @iRVOne M sM :=
    CanonicalStructure.normalize_fun Fn.rvOne Fin.elim0 (fun i => i.elim0)
  have huN : uN = (1 : @CanonicalRV.RVSort M N) := by
    apply Subtype.ext
    exact (@RVOperations.one_val M sM hM).trans (hOne.symm.trans (@RVOperations.one_val M N hN).symm)
  have hLt : Values.vrv u < Values.vrv t := by
    change Values.vrv (1 : CanonicalRV.RVSort M) < Values.vrv t
    rw [RVOperations.vrv_one,htδ]
    exact hδ
  have hRel : iLe u.val t.val ∧ ¬ iLe t.val u.val :=
    ⟨(Values.vrv_le_iff u t).mp hLt.le,
      fun h => not_le_of_gt hLt ((Values.vrv_le_iff t u).mpr h)⟩
  have hLtN : @Values.vrv M N hN uN < @Values.vrv M N hN tN := by
    apply lt_of_le_not_ge
    · apply (@Values.vrv_le_iff M N hN uN tN).mpr
      exact (rv_le_normalize u.val t.val u.property t.property).mpr hRel.1
    · intro h
      exact hRel.2 ((rv_le_normalize t.val u.val t.property u.property).mp
        ((@Values.vrv_le_iff M N hN tN uN).mp h))
  refine ⟨β,?_⟩
  change (1 : @Values.GammaTop M N hN) < @Values.vrv M N hN tN
  rw [huN,@RVOperations.vrv_one M N hN] at hLtN
  exact hLtN

end IntegrationInACVF.Section3ACVF.NormalizedNontrivialValue
