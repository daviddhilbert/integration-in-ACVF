import Integration7.VolumePartition
import Integration7.VolumeRestrictionIdentifications
import Integration7.VolumeCoproductIsomorphism
import Integration7.RVVolumeInverse

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeSplitComplement (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (A B : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hB : B.carrier ⊆ U.underlying.obj.domain.carrier) :
    RVVolumeIso (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)
      ((U.restrict (B.sdiff A) (fun _ h => hB h.1)).coprod
        (U.restrict (U.underlying.obj.domain.sdiff (A.union B)) Set.sdiff_subset)) := by
  let R := U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset
  let D := B.sdiff A
  let E := R.underlying.obj.domain.sdiff D
  have hD : D.carrier ⊆ R.underlying.obj.domain.carrier := fun _ h => ⟨hB h.1, h.2⟩
  have hE : E.carrier ⊆ U.underlying.obj.domain.carrier := fun _ h => h.1.1
  have he : E.carrier = (U.underlying.obj.domain.sdiff (A.union B)).carrier := by
    ext x
    constructor
    · rintro ⟨⟨hu, hna⟩, hn⟩
      refine ⟨hu, ?_⟩
      rintro (ha | hb)
      · exact hna ha
      · exact hn ⟨hb, hna⟩
    · rintro ⟨hu, hn⟩
      exact ⟨⟨hu, fun ha => hn (Or.inl ha)⟩, fun h => hn (Or.inr h.1)⟩
  let eD := volumeRestrictionTransIso hc C U (U.underlying.obj.domain.sdiff A) D Set.sdiff_subset hD
  let eE := (volumeRestrictionTransIso hc C U (U.underlying.obj.domain.sdiff A) E
    Set.sdiff_subset Set.sdiff_subset).trans hc C
      (volumeRestrictionCarrierIso hc C U E (U.underlying.obj.domain.sdiff (A.union B))
        hE Set.sdiff_subset he)
  exact ((volumeComplementPartitionIso hc C R D hD).symm hc C).trans hc C (eD.coprod hc C eE)

end IntegrationInACVF.Section7
