import IntegrationSection3ACVF.RVDifferencePairs

/-! Every RV class with the value of a difference of two points of an
open ball is realized as a difference at any of its base points. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RVInputFibre

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem translate_mem_of_value {A : Set M} (ho : PaperBalls.IsOpenBall A)
    (x y r : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hr : Values.vfValueHom r = Values.vfValueHom (y-x)) : (x+r).val ∈ A := by
  rcases ho with h | ⟨a,γ,h⟩
  · exact h.symm ▸ (x+r).property
  · rw [h] at hx hy ⊢
    obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative γ
    have hxv := (GammaCosetGeometry.gammaBall_mem_valuation v hv a s γ hs x).mp hx
    have hyv := (GammaCosetGeometry.gammaBall_mem_valuation v hv a s γ hs y).mp hy
    have hrv : v r = v (y-x) := le_antisymm
      ((hv _ _).mp ((Values.vf_pred_iff_gamma_le r (y-x)).mpr hr.symm.le))
      ((hv _ _).mp ((Values.vf_pred_iff_gamma_le (y-x) r).mpr hr.le))
    have hd : v (y-x) < v s := by
      have he : (y-a)-(x-a) = y-x := by ring
      simpa only [he] using v.map_sub_lt hyv hxv
    apply (GammaCosetGeometry.gammaBall_mem_valuation v hv a s γ hs (x+r)).mpr
    have he : (x+r)-a = (x-a)+r := by ring
    rw [he]
    exact v.map_add_lt hxv (hrv.symm ▸ hd)

theorem value_fibre_realized {A : Set M} (ho : PaperBalls.IsOpenBall A)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (t : CanonicalRV.RVSort M) (ht : Values.vrv t = Values.vfValueHom (y-x)) :
    ∃ z : VFType (M := M), z.val ∈ A ∧ difference z.val x.val = t.val := by
  obtain ⟨r,hr⟩ := CanonicalRV.encodedRv_surjective t
  have hrv : Values.vfValueHom r = Values.vfValueHom (y-x) := (congrArg Values.vrv hr).trans ht
  refine ⟨x+r,translate_mem_of_value ho x y r hx hy hrv,?_⟩
  rw [difference_vf,show (x+r)-x = r by ring]
  exact congrArg Subtype.val hr

end IntegrationInACVF.Section3ACVF.RVInputFibre
