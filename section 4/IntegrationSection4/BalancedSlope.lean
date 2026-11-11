import IntegrationSection4.Cells
import IntegrationSection4.InverseDifferenceGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.BalancedSlope

open BalancedFibres Cells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem value_sub_swap (x y : VF (M := M)) :
    Values.vfValueHom (x-y) = Values.vfValueHom (y-x) := by
  apply (Values.valueEquiv Values.presentationValuation Values.presentation_compatible).injective
  change Values.valueEquiv Values.presentationValuation Values.presentation_compatible
    (Values.vrv (CanonicalRV.encodedRv (x-y))) =
    Values.valueEquiv Values.presentationValuation Values.presentation_compatible
      (Values.vrv (CanonicalRV.encodedRv (y-x)))
  rw [Values.valueEquiv_apply_vf,Values.valueEquiv_apply_vf]
  exact Values.presentationValuation.restrict_inj.mpr (Values.presentationValuation.map_sub_swap x y)

/-- Remark 4.6: the actual Gamma slope is the ratio of the two RV paradigms.
Both paradigms are nonzero in the nondegenerate case. -/
theorem remark_4_6 {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hne : t₁ ≠ rv (0 : VF (M := M))) (a : VF (M := M)) (ha : a ∈ D)
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s) :
    s.val = Values.vrv t₂ / Values.vrv t₁ := by
  obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective t₁
  let x := a-u
  have hx : rv (a-x) = t₁ := by
    have he : a-x = u := by dsimp [x]; ring
    rw [he]
    exact Subtype.ext (congrArg Subtype.val hu)
  have hh := (Set.ext_iff.mp (h.horizontal a ha) x).mpr hx
  have hxD : x ∈ D := hh.1
  have hv : rv (f x-f a) = t₂ := (Set.ext_iff.mp (h.vertical a ha) (f x)).mp hh.2
  have hInput : Values.vfValueHom (x-a) = Values.vrv t₁ := by
    rw [value_sub_swap x a]
    exact congrArg Values.vrv hx
  have hOutput : Values.vfValueHom (f x-f a) = Values.vrv t₂ := congrArg Values.vrv hv
  have hSlope := hLin a x ⟨a,ha,rfl⟩ ⟨x,hxD,rfl⟩
  have hfa : (⟨rawMap f a.val,rawMap_vf f D a.val ⟨a,ha,rfl⟩⟩ : VFType (M := M)) = f a :=
    Subtype.ext (rawMap_on f a)
  have hfx : (⟨rawMap f x.val,rawMap_vf f D x.val ⟨x,hxD,rfl⟩⟩ : VFType (M := M)) = f x :=
    Subtype.ext (rawMap_on f x)
  change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) =
    s.val * Values.vfValueHom (x-a) at hSlope
  rw [hfa,hfx,hInput,hOutput] at hSlope
  have ht : Values.vrv t₁ ≠ 0 := by
    intro he
    apply hne
    have ht0 : t₁.val = iRVZero := (Values.vrv_eq_infinity_iff t₁).mp (he.trans Values.infinity_eq_zero.symm)
    apply Subtype.ext
    exact ht0.trans ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).symm
  exact (eq_div_iff ht).mpr hSlope.symm

end IntegrationInACVF.Section4.BalancedSlope
