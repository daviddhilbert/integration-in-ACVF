module

public import Integration7.MixedHeadFibres
public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.FrozenHeadVolumeIntegrals
public import Integration7.HeadFibreDensityGraphs
public import Integration7.HeadFibreContractionSources

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary degree-zero families have actual unary frozen fibres.
Their VF realization retains the unit density, and its density graph
is the literal frozen density graph of the original family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable {C : BaseContext M}

def OrdinaryVFVolumeFamily.headFibre (F : OrdinaryVFVolumeFamily C (n+1) a)
    (x : Fin n → VFType (M := M)) : OrdinaryVFVolumeFamily (vfParameterVolumeContext C x) 1 a where
  domain := (mixedHeadFibre F.domain x).extend (vfParameterVolumeContext_contains C x)
  finite_labels y := F.finite_labels (Fin.cons (y 0) x)

def OrdinaryVFVolumeFamily.extendContext (F : OrdinaryVFVolumeFamily C n a)
    {D : BaseContext M} (hD : (C.base : Set M) ⊆ (D.base : Set M)) : OrdinaryVFVolumeFamily D n a where
  domain := F.domain.extend hD
  finite_labels := F.finite_labels

def OrdinaryVFVolumeFamily.frozenHeadFamily
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M)) :
    OrdinaryVFVolumeFamily (frozenHeadVolumeContext hc C x) 1 a :=
  (F.headFibre x).extendContext (frozen_head_volume_context_contains hc C x)

theorem ordinary_head_fibre_density_contraction_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : BaseContext M)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    extendBase (coordinateFibre (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain) 0 (headFrozenTuple x))
      (head_fibre_contraction_base_subset C D x hD) =
    nativeMixedVolumeDomain hc (((F.headFibre x).extendContext hD).fullVFObject.densityGraph.domain) := by
  apply PresentedSet.eq_of_carrier_eq
  ext p
  change coordinateInsert 0 (headFrozenTuple x) p ∈ (volumeDensityGraph F.fullVFObject.form).carrier ↔
    p ∈ (volumeDensityGraph ((F.headFibre x).extendContext hD).fullVFObject.form).carrier
  rw [coordinateInsert_head]
  rcases p with ⟨y,r⟩
  rw [volume_density_graph_mem_iff,volume_density_graph_mem_iff]
  rfl

def ordinaryHeadFibreStandardContraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : BaseContext M)
    (F : OrdinaryVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    StandardContraction (nativeMixedVolumeDomain hc (((F.headFibre x).extendContext hD).fullVFObject.densityGraph.domain))
      (Equiv.refl _) := by
  let R := (headCoordinateFibreContraction T x).extendBase (head_fibre_contraction_base_subset C D x hD)
  exact {
    arity := R.arity
    target := R.target
    program := orderedCastSource R.program (congrArg (fun A => vfPermutationImage A (Equiv.refl _))
      (ordinary_head_fibre_density_contraction_source hc D F x hD)) }

end IntegrationInACVF.Section7
