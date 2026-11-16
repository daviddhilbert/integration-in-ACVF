module

public import Integration7.MixedVFBaseBijections

@[expose] public section

/-! The unweighted pushforward of an actual selected family along a
definable VF base bijection retains all RV coordinates and transports the
original density by the actual inverse mixed-family bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}
variable {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}

def SelectedVFVolumeFamily.pushforwardBase (F : SelectedVFVolumeFamily C n a k)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    SelectedVFVolumeFamily C n a k where
  domain := (mixedVFBaseMap φ F.domain hF).image
  selected := F.selected
  finite_selected := mixed_vf_base_image_finite_selected φ hφ F.domain hF F.selected F.finite_selected
  form := F.form.pullback ((mixedVFBaseMap φ F.domain hF).toImage.inverse
    (mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF))

theorem SelectedVFVolumeFamily.pushforwardBase_selected (F : SelectedVFVolumeFamily C n a k)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    (F.pushforwardBase φ hφ hF).selected = F.selected := rfl

theorem SelectedVFVolumeFamily.pushforwardBase_density (F : SelectedVFVolumeFamily C n a k)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (p : F.domain) :
    (F.pushforwardBase φ hφ hF).form.value ((mixedVFBaseMap φ F.domain hF).toImage p) = F.form.value p := by
  change F.form.value ((mixedVFBaseMap φ F.domain hF).toImage.inverse _
    ((mixedVFBaseMap φ F.domain hF).toImage p)) = F.form.value p
  rw [Map.inverse_apply]

theorem SelectedVFVolumeFamily.pushforwardBase_fibre (F : SelectedVFVolumeFamily C n a k)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (y : Y) (r : Fin a → CanonicalRV.RVSort M) :
    (y.val,r) ∈ (F.pushforwardBase φ hφ hF).domain.carrier ↔
      ((φ.inverse hφ y).val,r) ∈ F.domain.carrier := by
  constructor
  · rintro ⟨p,hp⟩
    have hBase : (φ ⟨p.val.1,hF p⟩).val = y.val := congrArg Prod.fst hp
    have hx : p.val.1 = (φ.inverse hφ y).val := congrArg Subtype.val
      (hφ.1 (Subtype.ext (hBase.trans (congrArg Subtype.val (Map.apply_inverse φ hφ y)).symm)))
    have hr : p.val.2 = r := congrArg Prod.snd hp
    have he : p.val = ((φ.inverse hφ y).val,r) := Prod.ext hx hr
    exact he ▸ p.property
  · intro hr
    let p : F.domain := ⟨((φ.inverse hφ y).val,r),hr⟩
    refine ⟨p,?_⟩
    change ((φ ⟨(φ.inverse hφ y).val,hF p⟩).val,r) = (y.val,r)
    exact Prod.ext (congrArg Subtype.val (Map.apply_inverse φ hφ y)) rfl

end IntegrationInACVF.Section7
