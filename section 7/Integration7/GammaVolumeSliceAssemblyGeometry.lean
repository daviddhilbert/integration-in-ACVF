import Integration7.GammaVolumeSliceDensityAssembly
import Integration7.GammaVolumePresentationGeometry
import Integration7.GammaVolumeParameterGeometry
import Integration7.GammaCoordinateDensityGraphs

/-! Coordinate-density objects and slice reassembly retain their full
original-Gamma geometry. The reassembly chart is the actual label projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV rvObjectArity rvObjectDomain GammaRVFiniteObject)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}

theorem gamma_coordinate_density_object_graphs
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (e+(k+1))) (hUC : U.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object))
    (hNZ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero) :
    VolumeObjectGamma (gammaCoordinateDensityObject hc C U hUC δ hNZ) B := by
  constructor
  · exact canonical_gamma_object_volume_graph hc (FiniteRV.gammaObjectAtExtend U hUC)
  · exact gamma_coordinate_density_graph _ (canonical_gamma_object_domain_graph hc (FiniteRV.gammaObjectAtExtend U hUC))
      δ (fun _ => rfl)

theorem gamma_volume_slice_assembly_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (e+(k+1))) (hUC : U.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object))
    (hNZ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (BP : IdentityIndexPresentation B e) (N : ℕ)
    (P : ((gammaVolumeSliceDensitySchema U δ).withBound N).IndexedPresentation BP)
    (hPC : P.finite.codes ⊆ (C.base : Set M)) :
    (gammaVolumeSliceDensityAssemblyIso hc C U hUC δ hNZ BP N P hPC).GammaDefinable B :=
  gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real (Fin.natAdd e))
    (gamma_essential_volume_domain _ (P.gamma_object hc C hPC).coordinates) (fun _ => rfl)

end IntegrationInACVF.Section7
