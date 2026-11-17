module

public import Integration7.FieldBaseAppendedIntegralIndependence
public import Integration7.FrozenHeadIntegralValues

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Genuine named-row common blowups determine the actual appended
frozen fibre integral, over its proved definable-closure context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_family_frozen_head_appended_integral_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hCommon : ∀ z, VolumeBlowupEquivalent (F.rowInContext z) (G.rowInContext z))
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ F x=selectedFamilyFrozenHeadAppendedIntegral hc C Ξ G x := by
  let D := frozenHeadVolumeContext hc C x
  let hD := frozen_head_volume_context_contains hc C x
  apply selected_family_field_appended_integral_independent hc D Ξ hΞ
    (definablyClosedVolumeContextField hc (vfParameterVolumeContext C x))
    (frozen_head_volume_context_common_names hc C Ξ hNames x) γ hγ hγ1
  intro y
  have eF := selectedHeadFibreRowIso hc C D F x hD y
  have eG := selectedHeadFibreRowIso hc C D G x hD y
  have h := (hCommon (Fin.cons (y 0) x)).extend (head_fibre_row_context_contains C D x hD y)
  exact (VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext D y) (eF.symm hc _)).trans hc _
    (h.trans hc _ (VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext D y) eG))
end IntegrationInACVF.Section7
