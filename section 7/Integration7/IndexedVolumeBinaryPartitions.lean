import Integration7.IndexedVolumeRestrictions
import Integration7.VolumePartition
import Integration7.VolumeCoproductIsomorphism
import Integration7.RVVolumeComposition
import IntegrationSection6.GammaGraphPresentationRestriction
import IntegrationSection6.IndexedSetPartitions

/-! Two definable index regions give the actual volume partition
isomorphism, with the original index volume and fibre density on each part. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV Point GammaSetDefinable gammaLogicInput)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def indexedVolumeBinaryIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (E : Set (Fin p → RV (M := M))) (hET : E ⊆ T)
    (hEΓ : GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ E})
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M)) :
    let BPA := BP.restrictDomain E hET hEΓ
    let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
    ∀ (PA : F.IndexedPresentation BPA) (PC : F.IndexedPresentation BPC)
      (hPA : PA.finite.codes ⊆ (C.base : Set M)) (hPC : PC.finite.codes ⊆ (C.base : Set M)),
      RVVolumeIso ((PA.inContext hc C hPA).toObject.coprod (PC.inContext hc C hPC).toObject)
        (P.inContext hc C hP).toObject := by
  dsimp only
  let BPA := BP.restrictDomain E hET hEΓ
  let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
  intro PA PC hPA hPC
  let U := (P.inContext hc C hP).toObject
  let A := (PA.inContext hc C hPA).underlying.obj.domain
  have hA : A.carrier = indexedDomain E (fun t => F.object.rowDomain (rvValues t)) :=
    GammaVolumeGraphPresentation.inContext_domain hc C PA hPA
  have hAU : A.carrier ⊆ U.underlying.obj.domain.carrier := by
    intro x hx
    apply (Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C P hP) x).mpr
    exact indexedDomain_mono hET _ ((Set.ext_iff.mp hA x).mp hx)
  have hComp : (U.underlying.obj.domain.sdiff A).carrier =
      indexedDomain (T \ E) (fun t => F.object.rowDomain (rvValues t)) := by
    change U.underlying.obj.domain.carrier \ A.carrier = _
    rw [hA]
    exact (congrArg (fun X => X \ indexedDomain E (fun t => F.object.rowDomain (rvValues t)))
      (GammaVolumeGraphPresentation.inContext_domain hc C P hP)).trans (indexedDomain_sdiff T E _)
  let eA := indexedVolumeRestrictionIso hc C F BP BPA hET
    (BP.restrictDomain_totalVolume E hET hEΓ) P PA hP hPA A hA hAU
  let eC := indexedVolumeRestrictionIso hc C F BP BPC (fun _ h => h.1)
    (BP.restrictDomain_totalVolume (T \ E) (fun _ h => h.1)
      ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)) P PC hP hPC
    (U.underlying.obj.domain.sdiff A) hComp Set.sdiff_subset
  exact (eA.coprod hc C eC).trans hc C (volumeComplementPartitionIso hc C U A hAU)

end IntegrationInACVF.Section7
