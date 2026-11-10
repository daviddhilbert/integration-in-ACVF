import IntegrationSection3ACVF.RVValueShellGeometry

/-! Strict error estimates and recovery of an affine RV difference. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.RVErrorComparison

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem error_value_gt (x y : VFType (M := M)) (hy : y ≠ 0)
    (hRV : CanonicalRV.encodedRv x = CanonicalRV.encodedRv y) :
    Values.vfValueHom y < Values.vfValueHom (x-y) := by
  have hn := (CanonicalRV.encoded_eq_iff_close x.property y.property
    (fun h => hy (Subtype.ext h))).mp (congrArg Subtype.val hRV)
  apply lt_of_not_ge
  intro he
  exact hn ((Values.vf_pred_iff_gamma_le y (x-y)).mpr he)

theorem affine_difference (x y e c fx fy fe : VFType (M := M))
    (hc : c ≠ 0) (hxy : y ≠ x)
    (hError : Values.vfValueHom (fy-fe-c*(y-e)) = Values.vfValueHom (fx-fe-c*(x-e)))
    (hSmall : Values.vfValueHom (c*(y-x)) < Values.vfValueHom (fx-fe-c*(x-e))) :
    CanonicalRV.encodedRv (fy-fx) = CanonicalRV.encodedRv (c*(y-x)) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hx : v (fx-fe-c*(x-e)) < v (c*(y-x)) := by
    apply lt_of_not_ge
    intro he
    exact not_le_of_gt hSmall
      ((Values.vf_pred_iff_gamma_le (c*(y-x)) (fx-fe-c*(x-e))).mp ((hv _ _).mpr he))
  have hye : v (fy-fe-c*(y-e)) = v (fx-fe-c*(x-e)) := by
    apply le_antisymm
    · exact (hv _ _).mp ((Values.vf_pred_iff_gamma_le _ _).mpr hError.symm.le)
    · exact (hv _ _).mp ((Values.vf_pred_iff_gamma_le _ _).mpr hError.le)
  have hdiff : v ((fy-fx)-c*(y-x)) < v (c*(y-x)) := by
    have he : (fy-fx)-c*(y-x) = (fy-fe-c*(y-e))-(fx-fe-c*(x-e)) := by ring
    rw [he]
    exact v.map_sub_lt (hye.symm ▸ hx) hx
  apply Subtype.ext
  apply (CanonicalRV.encoded_eq_iff_close (fy-fx).property (c*(y-x)).property
    (fun he => (mul_ne_zero hc (sub_ne_zero.mpr hxy)) (Subtype.ext he))).mpr
  intro hp
  exact not_le_of_gt hdiff ((hv _ _).mp hp)

end IntegrationInACVF.Section3ACVF.RVErrorComparison
