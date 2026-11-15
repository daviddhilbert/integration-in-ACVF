import Integration7.HeadFibreDensityGraphs
import Integration7.HeadFibreRawVolumePresentation
import Integration7.ContractionParameterExtension
import IntegrationSection6.ProgramEqualityTransport

/-! The inherited unary head contraction is an actual contraction of
the density graph of the frozen family. Equality transport retains its
literal target and all selected volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem head_fibre_contraction_base_subset (C D : BaseContext M)
    (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    coordinateFibreBase (C.base : Set M) 0 (headFrozenTuple x) ⊆ (D.base : Set M) := by
  rw [head_coordinate_fibre_base]
  exact (vfParameterVolumeContext_contains C x).trans hD

theorem head_fibre_density_contraction_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    extendBase (coordinateFibre (nativeMixedVolumeDomain hc F.densityGraph.domain) 0 (headFrozenTuple x))
      (head_fibre_contraction_base_subset C D x hD) =
    nativeMixedVolumeDomain hc (((F.headFibre x).extendContext hD).densityGraph.domain) := by
  apply PresentedSet.eq_of_carrier_eq
  ext p
  change coordinateInsert 0 (headFrozenTuple x) p ∈ (volumeDensityGraph F.form).carrier ↔
    p ∈ (volumeDensityGraph ((F.headFibre x).extendContext hD).form).carrier
  rw [coordinateInsert_head]
  rcases p with ⟨y,r⟩
  rw [volume_density_graph_mem_iff,volume_density_graph_mem_iff]
  rfl

def headFibreStandardContraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    StandardContraction (nativeMixedVolumeDomain hc (((F.headFibre x).extendContext hD).densityGraph.domain))
      (Equiv.refl _) := by
  let R := (headCoordinateFibreContraction T x).extendBase (head_fibre_contraction_base_subset C D x hD)
  exact {
    arity := R.arity
    target := R.target
    program := orderedCastSource R.program (congrArg (fun A => vfPermutationImage A (Equiv.refl _))
      (head_fibre_density_contraction_source hc C D F x hD)) }

end IntegrationInACVF.Section7
