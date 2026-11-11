import Section9.GaussEvaluation

/-! Agreement of actual value groups and surjectivity of the actual
residue inclusion give immediate approximation, without a completeness,
henselianity or finite-degree hypothesis. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical IsLocalRing
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section2.ImmediateApproximationFromResidues

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem approximate (v : Valuation K Γ) (F : Subfield K)
    (hSame : ∀ x : K, ∃ a : F, v (a:K) = v x)
    (hResidue : Function.Surjective (residueFieldInclusion v F))
    (x : K) (hx : x ≠ 0) : ∃ c : F, v (x-(c:K)) < v x := by
  classical
  let A := (v.comap F.subtype).valuationSubring
  let B := v.valuationSubring
  obtain ⟨a,ha⟩ := hSame x
  have hva : v (a:K) ≠ 0 := ha ▸ v.ne_zero_iff.mpr hx
  have ha0 : (a:K) ≠ 0 := v.ne_zero_iff.mp hva
  have hzval : v (x/(a:K)) = 1 := by rw [map_div₀,ha,div_self (v.ne_zero_iff.mpr hx)]
  let z : B := ⟨x/(a:K),(Valuation.mem_valuationSubring_iff v _).mpr hzval.le⟩
  obtain ⟨t,ht⟩ := hResidue (residue B z)
  obtain ⟨b,hb⟩ := residue_surjective (R := A) t
  have hres : residue B z = residue B (valuationRingInclusion v F b) := by
    rw [← ht,← hb]
    exact ResidueField.map_residue _ _
  have hsmall : v (x/(a:K)-((b:F):K)) < 1 := by
    have hr : z-valuationRingInclusion v F b ∈ maximalIdeal B := by
      apply (residue_eq_zero_iff _).mp
      rw [map_sub,hres,sub_self]
    exact (Valuation.mem_maximalIdeal_iff K v).mp hr
  let c : F := a*(b:F)
  have he : x-(c:K) = (a:K)*(x/(a:K)-((b:F):K)) := by
    rw [mul_sub,mul_comm (a:K) (x/(a:K)),div_mul_cancel₀ _ ha0]
    rfl
  refine ⟨c,?_⟩
  calc
    v (x-(c:K)) = v (a:K)*v (x/(a:K)-((b:F):K)) := by rw [he,map_mul]
    _ < v (a:K)*1 := mul_lt_mul_of_pos_left hsmall (pos_iff_ne_zero.mpr hva)
    _ = v x := by rw [mul_one,ha]

end IntegrationInACVF.Section2.ImmediateApproximationFromResidues
