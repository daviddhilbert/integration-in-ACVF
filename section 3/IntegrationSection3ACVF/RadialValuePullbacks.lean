import IntegrationSection3ACVF.RadialRVImages

/-! The entire translated RV image of a radial VF domain is the full
Gamma pullback, with every proper code representative. Concrete closed,
half-open and closed-ray value intervals retain their exact endpoints. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RadialValuePullbacks

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem image_eq_pullback (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) :
    RadialRVImages.image a V = Values.gammaPullback {γ : Values.Gamma (M := M) | γ.val ∈ V} := by
  ext x
  constructor
  · intro hx
    have hx0 := RadialRVImages.subset_nonzero a V hV hx
    have hVal := (RadialRVImages.mem_image a V (⟨x,hx0.1⟩ : CanonicalRV.RVSort M)).mp hx
    exact ⟨hx0.1,hx0.2,hVal⟩
  · rintro ⟨hxRV,_,hVal⟩
    exact (RadialRVImages.mem_image a V (⟨x,hxRV⟩ : CanonicalRV.RVSort M)).mpr hVal

theorem infinity_not_Iic (τ : Values.Gamma (M := M)) : Values.infinity ∉ Set.Iic τ.val := by
  intro h
  exact τ.property (le_antisymm (Values.le_infinity τ.val) h)

theorem closed_image (a : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) :
    RadialRVImages.image a (Set.Icc ρ.val τ.val) = Values.gammaPullback (Set.Icc ρ τ) := by
  rw [image_eq_pullback a _ (fun h => infinity_not_Iic τ h.2)]
  rfl

theorem open_image (a : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) :
    RadialRVImages.image a (Set.Ioc ρ.val τ.val) = Values.gammaPullback (Set.Ioc ρ τ) := by
  rw [image_eq_pullback a _ (fun h => infinity_not_Iic τ h.2)]
  rfl

theorem whole_field_image (a : VFType (M := M)) (τ : Values.Gamma (M := M)) :
    RadialRVImages.image a (Set.Iic τ.val) = Values.gammaPullback (Set.Iic τ) := by
  rw [image_eq_pullback a _ (infinity_not_Iic τ)]
  rfl

end IntegrationInACVF.Section3ACVF.RadialValuePullbacks
