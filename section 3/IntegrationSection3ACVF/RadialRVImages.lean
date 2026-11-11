import IntegrationSection3ACVF.RadialQuotientGraph

/-! A radial VF domain has the entire corresponding RV value fibres as
its translated RV image. Zero is excluded exactly when infinity is absent
from the actual value domain; no representative is added to the final base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RadialRVImages

open RadialOpenClasses RVDifferencePairs

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def image (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M))) : Set M :=
  (fun x => difference x a.val) '' domain a V

theorem mem_image (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (t : CanonicalRV.RVSort M) : t.val ∈ image a V ↔ Values.vrv t ∈ V := by
  constructor
  · rintro ⟨x,hx,he⟩
    let xx : VFType (M := M) := ⟨x,hx.choose⟩
    have hEq : CanonicalRV.encodedRv (xx-a) = t := by
      apply Subtype.ext
      change iRv (xx-a).val = t.val
      exact (difference_vf xx a).symm.trans he
    have hV := (mem_domain a xx V).mp hx
    exact (congrArg Values.vrv hEq) ▸ hV
  · intro ht
    obtain ⟨r,hr⟩ := CanonicalRV.encodedRv_surjective t
    have hvEq : Values.vfValueHom r = Values.vrv t := congrArg Values.vrv hr
    have hv : Values.vfValueHom r ∈ V := hvEq.symm ▸ ht
    have hx : (a+r).val ∈ domain a V := (mem_domain a (a+r) V).mpr (by simpa only [add_sub_cancel_left] using hv)
    refine ⟨(a+r).val,hx,?_⟩
    change difference (a+r).val a.val = t.val
    rw [@difference_vf M sM hM (a+r) a,add_sub_cancel_left]
    exact congrArg Subtype.val hr

theorem subset_rv (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M))) :
    image a V ⊆ {t | iRV t} := by
  rintro t ⟨x,hx,rfl⟩
  let xx : VFType (M := M) := ⟨x,hx.choose⟩
  change iRV (difference xx.val a.val)
  rw [difference_vf]
  exact rv_mem hM (xx-a).property

theorem subset_nonzero (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) : image a V ⊆ {t | NonzeroRV t} := by
  intro t ht
  have htRV := subset_rv a V ht
  refine ⟨htRV,?_⟩
  intro ht0
  have h := (mem_image a V (⟨t,htRV⟩ : CanonicalRV.RVSort M)).mp ht
  have he := (Values.vrv_eq_infinity_iff (⟨t,htRV⟩ : CanonicalRV.RVSort M)).mpr ht0
  exact hV (he ▸ h)

end IntegrationInACVF.Section3ACVF.RadialRVImages
