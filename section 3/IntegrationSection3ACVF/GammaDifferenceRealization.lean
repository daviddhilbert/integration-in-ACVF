import IntegrationSection3ACVF.RVSlopeGamma

/-! The actual Gamma values of nonzero differences in an ordinary open
ball are precisely the open tail above its radius. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.GammaDifferenceRealization

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_pair (a : VFType (M := M)) (α γ : Values.Gamma (M := M)) (hαγ : α < γ) :
    ∃ x y : VFType (M := M), x.val ∈ gammaBall a α true ∧ y.val ∈ gammaBall a α true ∧
      y ≠ x ∧ Values.vfValueHom (y-x) = γ.val := by
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
  have hr0 : r ≠ 0 := by
    intro h
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [h,map_zero]
      exact Values.infinity_eq_zero.symm
    exact γ.property (hr.symm.trans hz)
  have he : (a+r)-a = r := by ring
  have hv : Values.vfValueHom ((a+r)-a) = γ.val := (congrArg Values.vfValueHom he).trans hr
  have hy : (a+r).val ∈ gammaBall a α true := by
    change ∃ hy : iVF (a+r).val, α.val ≤ Values.vfValueHom ((a+r)-a) ∧
      (true = true → ¬ Values.vfValueHom ((a+r)-a) ≤ α.val)
    refine ⟨(a+r).property,?_,?_⟩
    · exact hv.symm ▸ hαγ.le
    · intro _ h
      have he : γ.val ≤ α.val := hv ▸ h
      exact not_le_of_gt hαγ he
  have hne : a+r ≠ a := by
    intro h
    exact hr0 (add_left_cancel (h.trans (add_zero a).symm))
  exact ⟨a,a+r,BallEnlargementGeometry.gammaBall_centre_mem a α true,hy,hne,hv⟩

theorem difference_gt_radius (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (x y : VFType (M := M)) (hx : x.val ∈ gammaBall a α true)
    (hy : y.val ∈ gammaBall a α true) : α.val < Values.vfValueHom (y-x) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hxv := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr x).mp hx
  have hyv := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr y).mp hy
  have hdist : v (y-x) < v r := by
    have he : (y-a)-(x-a) = y-x := by ring
    simpa only [he] using v.map_sub_lt hyv hxv
  have hpaper : Values.vfValueHom r < Values.vfValueHom (y-x) := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨(Values.vf_pred_iff_gamma_le (y-x) r).mp ((hv _ _).mpr hdist.le),?_⟩
    intro h
    exact not_le_of_gt hdist ((hv _ _).mp ((Values.vf_pred_iff_gamma_le r (y-x)).mpr h))
  exact hr ▸ hpaper

end IntegrationInACVF.Section3ACVF.GammaDifferenceRealization
