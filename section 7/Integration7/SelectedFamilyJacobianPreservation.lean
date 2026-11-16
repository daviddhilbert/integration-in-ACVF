module

public import Integration7.InverseMixedVFBaseDensities
public import Integration7.SelectedFamilyJacobianPushforwards

@[expose] public section

/-! The actual Jacobian-corrected family map preserves its mixed VF
volume form. The inverse-density comparison is an established AE theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a k : ℕ}

theorem selected_family_jacobian_pushforward_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : Map X Y) (hφ : Function.Bijective φ)
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

end IntegrationInACVF.Section7
