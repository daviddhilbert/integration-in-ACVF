import Integration7.ElementaryBlowupIsomorphism
import Integration7.ElementaryBlowupRestriction
import Integration7.VolumePartition
import Integration7.VolumeRestrictionIdentifications
import Integration7.VolumeCoproductIsomorphism
import Integration7.RVVolumeComposition

/-! An actual elementary blowup splits over a definable source partition. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.ElementaryBlowup

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem sourcePreimage_complement {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S) :
    (b.sourcePreimage (U.underlying.obj.domain.sdiff A)).carrier =
      (W.underlying.obj.domain.sdiff (b.sourcePreimage A)).carrier := by
  ext x
  constructor
  · intro hx
    have hxW := b.sourcePreimage_subset (U.underlying.obj.domain.sdiff A) hx
    let w : W.underlying.obj.domain := ⟨x, hxW⟩
    have hp := (b.mem_sourcePreimage (U.underlying.obj.domain.sdiff A) w).mp hx
    exact ⟨hxW, fun h => hp.2 ((b.mem_sourcePreimage A w).mp h)⟩
  · rintro ⟨hxW, hn⟩
    let w : W.underlying.obj.domain := ⟨x, hxW⟩
    apply (b.mem_sourcePreimage (U.underlying.obj.domain.sdiff A) w).mpr
    exact ⟨(b.projection w).property, fun h => hn ((b.mem_sourcePreimage A w).mpr h)⟩

def partitionIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U W)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) :
    RVVolumeIso
      ((elementaryVolumeObject C (U.restrict A hA) (b.admissible.restrict A hA)).coprod
        (elementaryVolumeObject C (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)
          (b.admissible.restrict _ Set.sdiff_subset))) W := by
  let L := U.restrict A hA
  let R := U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset
  let hL := b.admissible.restrict A hA
  let hR := b.admissible.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset
  let eL := elementaryBlowupIso hc C (RVVolumeIso.refl hc C L)
    (elementaryVolumeBlowup C L hL) (b.restrict A hA)
  let eR := elementaryBlowupIso hc C (RVVolumeIso.refl hc C R)
    (elementaryVolumeBlowup C R hR) (b.restrict _ Set.sdiff_subset)
  let ecomp := volumeRestrictionCarrierIso hc C W
    (b.sourcePreimage (U.underlying.obj.domain.sdiff A))
    (W.underlying.obj.domain.sdiff (b.sourcePreimage A))
    (b.sourcePreimage_subset _) Set.sdiff_subset (b.sourcePreimage_complement A)
  exact (eL.coprod hc C (eR.trans hc C ecomp)).trans hc C
    (volumeComplementPartitionIso hc C W (b.sourcePreimage A) (b.sourcePreimage_subset A))

end IntegrationInACVF.Section7.ElementaryBlowup
