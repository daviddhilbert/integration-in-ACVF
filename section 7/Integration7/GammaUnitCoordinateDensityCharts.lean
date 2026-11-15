import Integration7.GammaUnitVolumeIsoRealization
import Integration7.GammaVolumeSliceAssemblyGeometry

/-! A retained unit density and the literal unit form define the same
actual volume object. The label identity is an original-Gamma chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

theorem gamma_unit_coordinate_density_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B 1) (hUC : U.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object))
    (hNZ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (hOne : ∀ u : (gammaCoordinateDensityObject (e := 0) (k := 0) hc C U hUC δ hNZ).underlying.obj.domain,
      u.val δ = 1) :
    ∃ e : RVVolumeIso (gammaUnitVolumeObject hc C U hUC)
      (gammaCoordinateDensityObject (e := 0) (k := 0) hc C U hUC δ hNZ), e.GammaDefinable B := by
  let V := gammaCoordinateDensityObject (e := 0) (k := 0) hc C U hUC δ hNZ
  let W := gammaUnitVolumeObject hc C U hUC
  let f : Map V.underlying.obj.domain W.underlying.obj.domain := Map.id _
  have hf : Function.Bijective f := Function.bijective_id
  let g : RVVolumeIso V W := RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf (fun _ => rfl)))
    (fun _ => rfl) (fun u => (hOne u).symm)
  have hg : g.GammaDefinable B := gamma_volume_iso_of_label_identity hc g
    (gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc C U hUC δ hNZ) rfl (fun _ => rfl)
  exact ⟨g.symm hc C,hg.symm hc C B⟩

end IntegrationInACVF.Section7
