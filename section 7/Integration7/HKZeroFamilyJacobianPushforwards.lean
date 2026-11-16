import Integration7.HKZeroVolumeFamilies
import Integration7.SelectedFamilyJacobianPreservation

/-! Weighted-zero functions push forward along a VF base bijection.
Only the original RV density is multiplied by the inverse base Jacobian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}
variable {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}

def ZeroVFVolumeFamily.pushforwardBase (F : ZeroVFVolumeFamily C n a)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    ZeroVFVolumeFamily C n a where
  domain := (mixedVFBaseMap φ F.domain hF).image
  finite_labels y := by
    have h := mixed_vf_base_image_finite_selected φ hφ F.domain hF (Fin.elim0 : Fin 0 → Fin a)
      (fun x _ => (F.finite_labels x).subset (fun _ hr => hr.1)) y Fin.elim0
    exact h.subset (fun r hr => ⟨hr,Subsingleton.elim _ _⟩)
  form := F.form.pullback ((mixedVFBaseMap φ F.domain hF).toImage.inverse
    (mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF))

theorem ZeroVFVolumeFamily.pushforwardBase_density (F : ZeroVFVolumeFamily C n a)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (p : F.domain) :
    (F.pushforwardBase φ hφ hF).form.value ((mixedVFBaseMap φ F.domain hF).toImage p) = F.form.value p := by
  change F.form.value ((mixedVFBaseMap φ F.domain hF).toImage.inverse _
    ((mixedVFBaseMap φ F.domain hF).toImage p)) = F.form.value p
  rw [Map.inverse_apply]

theorem ZeroVFVolumeFamily.pushforwardBase_fibre (F : ZeroVFVolumeFamily C n a)
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


def ZeroVFVolumeFamily.jacobianPushforward (F : ZeroVFVolumeFamily C n a)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    ZeroVFVolumeFamily C n a where
  domain := (F.pushforwardBase φ hφ hF).domain
  finite_labels := (F.pushforwardBase φ hφ hF).finite_labels
  form := ((pureVFInverseJacobianDensityForm φ hφ).pullback
    (mixedVFBaseImageProjection φ F.domain hF)).mul (F.pushforwardBase φ hφ hF).form

theorem ZeroVFVolumeFamily.jacobianPushforward_density (F : ZeroVFVolumeFamily C n a)
    (φ : Map X Y) (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (p : F.domain) :
    (F.jacobianPushforward φ hφ hF).form.value ((mixedVFBaseMap φ F.domain hF).toImage p) =
      (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨p.val.1,hF p⟩) * F.form.value p := by
  change (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨p.val.1,hF p⟩) *
    (F.pushforwardBase φ hφ hF).form.value ((mixedVFBaseMap φ F.domain hF).toImage p) = _
  rw [F.pushforwardBase_density]

theorem zero_family_jacobian_pushforward_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : ZeroVFVolumeFamily C n a) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    PreservesVFVolume F.form (F.jacobianPushforward φ hφ hF).form
      (mixedVFBaseMap φ F.domain hF).toImage := by
  let f := (mixedVFBaseMap φ F.domain hF).toImage
  let hf := mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF
  have hPres := preserves_inverse_jacobian_vf_volume hc C hn f hf F.form
  have hDensity := inverse_mixed_vf_base_density_agreement_ae hc C hn φ hφ F.domain hF
  apply (vfAlmostEverywhere_and hc C hPres hDensity).mono
  rintro p ⟨⟨J,hJ,hVolume⟩,hD⟩
  refine ⟨J,hJ,?_⟩
  rw [F.jacobianPushforward_density]
  rw [inverse_jacobian_vf_volume_form_value,Map.inverse_apply] at hVolume
  rw [hD] at hVolume
  exact hVolume


end IntegrationInACVF.Section7.HK
