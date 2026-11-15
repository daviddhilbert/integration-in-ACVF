import Integration7.SelectedTailVolumePreservation
import Integration7.SelectedFamilyJacobianPreservation
import Integration7.SelectedFamilyFullLifts

/-! The family Jacobian transformation induces a genuine full volume
bijection of its VF realizations, fixing all coefficient VF coordinates. -/
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

def selectedFamilyJacobianFullLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    VFVolumeBijection F.fullLift (F.jacobianPushforward φ hφ hF).fullLift := by
  let f := (mixedVFBaseMap φ F.domain hF).toImage
  have hf := mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF
  have hLabels : ∀ p : F.domain, (f p).val.2 = p.val.2 := fun _ => rfl
  exact {
    map := selectedTailLiftMap f hLabels F.selected
    bijective := selected_tail_lift_map_bijective f hf hLabels F.selected
    preserves := preserves_vf_volume_selected_tail hc C (Nat.zero_lt_succ k)
      f hLabels F.form (F.jacobianPushforward φ hφ hF).form F.selected
      (selected_family_jacobian_pushforward_preserves_volume hc C hn F φ hφ hF) }

end IntegrationInACVF.Section7
