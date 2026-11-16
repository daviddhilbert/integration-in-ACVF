module

public import Integration7.MixedHeadFibres
public import Integration7.HKZeroVolumeFamilies
public import Integration7.FrozenHeadVolumeIntegrals
public import Integration7.HeadFibreDensityGraphs
public import Integration7.HeadFibreContractionSources

@[expose] public section

/-! Weighted-zero families have actual frozen unary fibres, with their
original form pulled back along the literal VF insertion map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable {C : BaseContext M}

def ZeroVFVolumeFamily.headFibre (F : ZeroVFVolumeFamily C (n+1) a)
    (x : Fin n → VFType (M := M)) : ZeroVFVolumeFamily (vfParameterVolumeContext C x) 1 a where
  domain := (mixedHeadFibre F.domain x).extend (vfParameterVolumeContext_contains C x)
  finite_labels y := F.finite_labels (Fin.cons (y 0) x)
  form := (F.form.mixedHeadFibre x).extend (vfParameterVolumeContext_contains C x)

def ZeroVFVolumeFamily.extendContext (F : ZeroVFVolumeFamily C n a)
    {D : BaseContext M} (hD : (C.base : Set M) ⊆ (D.base : Set M)) : ZeroVFVolumeFamily D n a where
  domain := F.domain.extend hD
  finite_labels := F.finite_labels
  form := F.form.extend hD

def ZeroVFVolumeFamily.frozenHeadFamily
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M)) :
    ZeroVFVolumeFamily (frozenHeadVolumeContext hc C x) 1 a :=
  (F.headFibre x).extendContext (frozen_head_volume_context_contains hc C x)

theorem zero_head_fibre_density_contraction_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : BaseContext M)
    (F : ZeroVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M))
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

def zeroHeadFibreStandardContraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (D : BaseContext M)
    (F : ZeroVFVolumeFamily C (n+1) a)
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
      (zero_head_fibre_density_contraction_source hc D F x hD)) }

end IntegrationInACVF.Section7.HK
