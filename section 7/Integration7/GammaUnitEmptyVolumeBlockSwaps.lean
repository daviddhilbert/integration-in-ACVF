module

public import Integration7.GammaUnitVolumeObjectGraphs
public import Integration7.GammaVolumePresentationGeometry
public import IntegrationSection6.GammaSwappedVolumes

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Swapping an empty old-volume block and the sole VF volume tag
does not change a unit-density volume object or its original-Gamma chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

theorem gamma_unit_empty_volume_block_swap_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B 1) (hUC : U.codes ⊆ (C.base : Set M)) :
    ∃ e : RVVolumeIso
      (gammaUnitVolumeObject hc C (gammaSwapVolumeBlocks (n := 1) (e := 0) U) hUC)
      (gammaUnitVolumeObject hc C U hUC), e.GammaDefinable B := by
  let V := gammaUnitVolumeObject hc C (gammaSwapVolumeBlocks (n := 1) (e := 0) U) hUC
  let W := gammaUnitVolumeObject hc C U hUC
  let f : Map V.underlying.obj.domain W.underlying.obj.domain := Map.id _
  have hf : Function.Bijective f := Function.bijective_id
  have hCoord : ∀ u, W.underlying.obj.value (f u) = V.underlying.obj.value u := by
    intro u
    funext i
    apply Subtype.ext
    change (gammaVolumeValue U.toGammaRVObject ⟨u.val,u.property⟩ i).val =
      (gammaVolumeValue U.toGammaRVObject ⟨u.val,u.property⟩ ((@finAddFlip 0 1) i)).val
    exact congrArg (fun j => (gammaVolumeValue U.toGammaRVObject ⟨u.val,u.property⟩ j).val)
      (Subsingleton.elim _ _)
  let e := RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord (fun _ => rfl)
  exact ⟨e,gamma_volume_iso_of_label_identity hc e
    (gamma_unit_volume_object_graphs hc C (gammaSwapVolumeBlocks (n := 1) (e := 0) U) hUC) rfl (fun _ => rfl)⟩

end IntegrationInACVF.Section7
