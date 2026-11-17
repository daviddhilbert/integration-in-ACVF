module

public import Integration7.IndexedVolumeCoordinateDensityIso
public import Integration7.GammaVolumePresentationGeometry
public import Integration7.GammaVolumeSliceAssemblyGeometry
public import Integration7.GammaVolumeSliceDensityAssembly

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An indexed presentation whose density is a retained label is
volume isomorphic to the actual canonical coordinate-density object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem gamma_indexed_volume_coordinate_density_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (P : F.IndexedPresentation BP)
    (hPC : P.finite.codes ⊆ (C.base : Set M)) (δ : Fin a)
    (hDensity : ∀ s ∈ T, ∀ r w, F.rowDensity (rvValues s) r w ↔
      r ∈ F.object.rowDomain (rvValues s) ∧ w 0 = r δ) :
    (indexedVolumeCoordinateDensityIso hc C F BP P hPC δ hDensity).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ (P.gamma_object hc C hPC) rfl (fun _ => rfl)

end IntegrationInACVF.Section7
