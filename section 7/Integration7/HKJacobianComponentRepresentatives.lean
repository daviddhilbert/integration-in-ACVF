module

public import Integration7.HKGradedAEVolumeJacobians

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The global Jacobian maps retain their literal family formulas.
The whole-space presentation equivalence introduces no new choices of
weighted rows or densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
  (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
variable (hφ : Function.Bijective φ)

theorem ae_zero_volume_component_jacobian_representative (F : ZeroVFVolumeFamily C (n+1) a) :
    aeVolumeComponentJacobianAddHom hc C φ hφ 0 (Quotient.mk _ ⟨a,F⟩) =
      Quotient.mk _ ⟨a,F.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)⟩ := by
  let g : SupportedVolumeFunctionComponent hc C (DefSet.univ _ _) 0 :=
    Quotient.mk _ ⟨a,⟨F,fun _ => Set.mem_univ _⟩⟩
  have he : (supportedVolumeComponentUnivEquiv hc C n 0).symm (Quotient.mk _ ⟨a,F⟩) = g :=
    (supportedVolumeComponentUnivEquiv hc C n 0).symm_apply_eq.mpr rfl
  change supportedVolumeComponentForgetAddHom hc C _ 0
    (supportedVolumeComponentJacobianAddHom hc C φ hφ 0
      ((supportedVolumeComponentUnivEquiv hc C n 0).symm (Quotient.mk _ ⟨a,F⟩))) = _
  rw [he]
  rfl

theorem ae_positive_volume_component_jacobian_representative (F : SelectedVFVolumeFamily C (n+1) a k) :
    aeVolumeComponentJacobianAddHom hc C φ hφ (k+1) (Quotient.mk _ ⟨a,F⟩) =
      Quotient.mk _ ⟨a,F.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)⟩ := by
  let g : SupportedVolumeFunctionComponent hc C (DefSet.univ _ _) (k+1) :=
    Quotient.mk _ ⟨a,⟨F,fun _ => Set.mem_univ _⟩⟩
  have he : (supportedVolumeComponentUnivEquiv hc C n (k+1)).symm (Quotient.mk _ ⟨a,F⟩) = g :=
    (supportedVolumeComponentUnivEquiv hc C n (k+1)).symm_apply_eq.mpr rfl
  change supportedVolumeComponentForgetAddHom hc C _ (k+1)
    (supportedVolumeComponentJacobianAddHom hc C φ hφ (k+1)
      ((supportedVolumeComponentUnivEquiv hc C n (k+1)).symm (Quotient.mk _ ⟨a,F⟩))) = _
  rw [he]
  rfl

end IntegrationInACVF.Section7.HK
