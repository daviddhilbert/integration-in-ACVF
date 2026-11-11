import IntegrationSection3ACVF.GammaLinearRestrictions
import IntegrationSection4.RadiusPreparationGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF
open GammaRadiusAtomicity

namespace IntegrationInACVF.Section4.LinearBallRadius

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The radii of actual ordinary open balls determine the slope of any
Gamma-linear surjection between them. No atomicity hypothesis is needed. -/
theorem slope_eq (a b : VFType (M := M)) (α β s : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hLin : GammaLinearity.GammaLinear (gammaBall a α true) f hfVF s)
    (hImage : f '' gammaBall a α true = gammaBall b β true) : s = β/α := by
  have hCut (γ : Values.Gamma (M := M)) : α < γ ↔ β < s*γ := by
    constructor
    · intro hαγ
      obtain ⟨x,y,hx,hy,_,hval⟩ := GammaDifferenceRealization.exists_pair a α γ hαγ
      let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
      let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
      have hfx : fx.val ∈ gammaBall b β true := hImage ▸ (show f x.val ∈ f '' gammaBall a α true from ⟨x.val,hx,rfl⟩)
      have hfy : fy.val ∈ gammaBall b β true := hImage ▸ (show f y.val ∈ f '' gammaBall a α true from ⟨y.val,hy,rfl⟩)
      have hOut := GammaDifferenceRealization.difference_gt_radius b β fx fy hfx hfy
      have hSlope := hLin x y hx hy
      change Values.vfValueHom (fy-fx) = s.val * Values.vfValueHom (y-x) at hSlope
      rw [hval,← Values.gamma_val_mul s γ] at hSlope
      rw [hSlope] at hOut
      exact hOut
    · intro hβγ
      obtain ⟨u,v,hu,hv,_,hval⟩ := GammaDifferenceRealization.exists_pair b β (s*γ) hβγ
      obtain ⟨x,hx,hxu⟩ := hImage.symm ▸ hu
      obtain ⟨y,hy,hyv⟩ := hImage.symm ▸ hv
      let X : VFType (M := M) := ⟨x,hx.1⟩
      let Y : VFType (M := M) := ⟨y,hy.1⟩
      have hfx : (⟨f x,hfVF _ hx⟩ : VFType (M := M)) = u := Subtype.ext hxu
      have hfy : (⟨f y,hfVF _ hy⟩ : VFType (M := M)) = v := Subtype.ext hyv
      have hSlope := hLin X Y hx hy
      change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) =
        s.val * Values.vfValueHom (Y-X) at hSlope
      rw [hfx,hfy,hval,Values.gamma_val_mul] at hSlope
      have hs0 : s.val ≠ 0 := fun h => s.property (h.trans Values.infinity_eq_zero.symm)
      have he : Values.vfValueHom (Y-X) = γ.val := mul_left_cancel₀ hs0 hSlope.symm
      have hIn := GammaDifferenceRealization.difference_gt_radius a α X Y hx hy
      rwa [he] at hIn
  have hp : s*(β/s) = β := by simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  have hle : β/s ≤ α := by
    apply le_of_not_gt
    intro h
    have hh := (hCut (β/s)).mp h
    rw [hp] at hh
    exact lt_irrefl β hh
  have hle' : α ≤ β/s := by
    apply le_of_not_gt
    intro h
    have hh := mul_lt_mul_right h s
    rw [hp] at hh
    exact lt_irrefl α ((hCut α).mpr hh)
  have he : α = β/s := le_antisymm hle' hle
  rw [he]
  exact (div_div_cancel β s).symm

/-- An open image of an ordinary ball under a Gamma-linear map has the
radius multiplied by the slope, and is centred at the image of the centre. -/
theorem image_ball (a : VFType (M := M)) (α s : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hLin : GammaLinearity.GammaLinear (gammaBall a α true) f hfVF s)
    (hOpen : PaperBalls.IsOpenBall (f '' gammaBall a α true)) :
    f '' gammaBall a α true = gammaBall
      (⟨f a.val,hfVF _ (BallEnlargementGeometry.gammaBall_centre_mem a α true)⟩ : VFType (M := M)) (s*α) true := by
  have ha := BallEnlargementGeometry.gammaBall_centre_mem a α true
  let b : VFType (M := M) := ⟨f a.val,hfVF _ ha⟩
  have hb : b.val ∈ f '' gammaBall a α true := ⟨a.val,ha,rfl⟩
  rcases hOpen with hWhole | ⟨c,β,hImage⟩
  · obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative (s*α)
    have hy : (b+r).val ∈ f '' gammaBall a α true := hWhole.symm ▸ (b+r).property
    obtain ⟨x,hx,hfx⟩ := hy
    let X : VFType (M := M) := ⟨x,hx.1⟩
    have hfx' : (⟨f x,hfVF _ hx⟩ : VFType (M := M)) = b+r := Subtype.ext hfx
    have hSlope := hLin a X ha hx
    change Values.vfValueHom ((_ : VFType (M := M))-b) = s.val * Values.vfValueHom (X-a) at hSlope
    rw [hfx',add_sub_cancel_left,hr,Values.gamma_val_mul] at hSlope
    have hs0 : s.val ≠ 0 := fun h => s.property (h.trans Values.infinity_eq_zero.symm)
    have he : Values.vfValueHom (X-a) = α.val := mul_left_cancel₀ hs0 hSlope.symm
    have hgt := GammaDifferenceRealization.difference_gt_radius a α a X ha hx
    rw [he] at hgt
    exact (lt_irrefl α.val hgt).elim
  · have hSlope := slope_eq a c α β s f hfVF hLin hImage
    have hβ : β = s*α := by rw [hSlope]; simp
    have hb' : b.val ∈ gammaBall c β true := hImage ▸ hb
    exact hImage.trans ((RadiusPreparationGeometry.recentre c b β hb').symm.trans (by rw [hβ]))

end IntegrationInACVF.Section4.LinearBallRadius
