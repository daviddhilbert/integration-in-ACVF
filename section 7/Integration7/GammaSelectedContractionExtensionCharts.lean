module

public import Integration7.SelectedContractionExtensionVolumeIso
public import Integration7.GammaVolumeSliceAssemblyGeometry
public import Integration7.GammaVolumeSliceDensityAssembly
public import IntegrationSection6.FiniteSelectedContractionSlices

@[expose] public section

/-! The actual selected contraction volume object is unchanged by
parameter enlargement. The label identity preserves all volume
coordinates and the retained density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section7 (gammaVolumeValue)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}

set_option maxHeartbeats 1600000 in
theorem gamma_positive_selected_contraction_extension_iso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D E : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (hDE : (D.base : Set M) ⊆ (E.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (hδ : ∀ u : U, (u.val.2 δ).val ≠ iRVZero) :
    (positiveSelectedContractionExtensionVolumeIso hc C D E hCD hDE hκ hs hreal hBC U hU ρ hfin T hT δ hδ).GammaDefinable B := by
  let RU := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfin T hT
  let e := positiveSelectedContractionExtensionVolumeIso hc C D E hCD hDE hκ hs hreal hBC U hU ρ hfin T hT δ hδ
  have hA : VolumeObjectGamma
      (gammaCoordinateDensityObject (e := k+1) (k := n) hc E RU (hCD.trans hDE)
        (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)) B :=
    gamma_coordinate_density_object_graphs (e := k+1) (k := n) hc E RU
      (hCD.trans hDE) (FiniteRV.contractionOldLabelIndex T δ)
      (normalized_contraction_retained_density_nonzero T δ hδ)
  exact gamma_volume_iso_of_label_identity hc e hA rfl (fun _ => rfl)

end IntegrationInACVF.Section7
