import IntegrationSection3ACVF.RVErrorComparison

/-! Distinct leading RV classes of the same value cannot cancel. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.RVLeadingDifference

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem value_sub (u v : VFType (M := M)) (hv0 : v ≠ 0)
    (hValue : Values.vfValueHom u = Values.vfValueHom v)
    (hRV : CanonicalRV.encodedRv u ≠ CanonicalRV.encodedRv v) :
    Values.vfValueHom (u-v) = Values.vfValueHom v := by
  obtain ⟨Γ,hΓ,w,hw⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have huv : w u = w v := (Values.vf_value_eq_iff w hw u v).mp hValue
  apply (Values.vf_value_eq_iff w hw (u-v) v).mpr
  apply le_antisymm
  · exact w.map_sub_le huv.le le_rfl
  · apply le_of_not_gt
    intro hlt
    apply hRV
    apply Subtype.ext
    apply (CanonicalRV.encoded_eq_iff_close u.property v.property
      (fun he => hv0 (Subtype.ext he))).mpr
    intro hp
    exact not_le_of_gt hlt ((hw _ _).mp hp)

end IntegrationInACVF.Section3ACVF.RVLeadingDifference
