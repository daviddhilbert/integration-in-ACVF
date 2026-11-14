import Integration7.VolumePartition
import Integration7.VolumeRestrictionIdentifications
import Integration7.VolumeCoproductIsomorphism
import Integration7.RVVolumeComposition
import Integration7.RVVolumeInverse

/-! Any two definable disjoint pieces covering an actual volume object
give its coordinate- and density-preserving coproduct partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeObjectPartitionIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (L R : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hL : L.carrier ⊆ U.underlying.obj.domain.carrier) (hR : R.carrier ⊆ U.underlying.obj.domain.carrier)
    (hCover : U.underlying.obj.domain.carrier = L.carrier ∪ R.carrier)
    (hDisj : Disjoint L.carrier R.carrier) : RVVolumeIso U ((U.restrict L hL).coprod (U.restrict R hR)) := by
  have hComp : (U.underlying.obj.domain.sdiff L).carrier = R.carrier := by
    ext r
    constructor
    · rintro ⟨hr,hn⟩
      rcases (Set.ext_iff.mp hCover r).mp hr with h | h
      · exact (hn h).elim
      · exact h
    · intro hr
      exact ⟨hR hr,fun hl => Set.disjoint_left.mp hDisj hl hr⟩
  let e := volumeRestrictionCarrierIso hc C U (U.underlying.obj.domain.sdiff L) R Set.sdiff_subset hR hComp
  exact ((volumeComplementPartitionIso hc C U L hL).symm hc C).trans hc C
    ((RVVolumeIso.refl hc C (U.restrict L hL)).coprod hc C e)

end IntegrationInACVF.Section7
