import Integration7.VolumeCoproduct
import Integration7.VolumeRelabeling
import IntegrationSection6.PartitionCoordinates

/-! Definable complementary pieces partition a volume object through an
actual coordinate- and density-preserving bijection. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def volumeComplementPartitionUnderlying (U : PositiveRVVolumeObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) :
    ((U.restrict A hA).coprod
      (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)).underlying ≅ U.underlying :=
  rvFiniteIsoOfAmbient (Section6.partitionIso U.underlying.obj A hA)

theorem volumeComplementPartitionUnderlying_left (U : PositiveRVVolumeObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) (a : A) :
    finiteIsoMap (volumeComplementPartitionUnderlying U A hA)
      (rvCoprodLeftMap (U.restrict A hA).underlying.obj
        (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj a) =
      ⟨a.val, hA a.property⟩ :=
  Subtype.ext (Section6.partitionIso_left U.underlying.obj A hA a)

theorem volumeComplementPartitionUnderlying_right (U : PositiveRVVolumeObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) (a : U.underlying.obj.domain.sdiff A) :
    finiteIsoMap (volumeComplementPartitionUnderlying U A hA)
      (rvCoprodRightMap (U.restrict A hA).underlying.obj
        (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj a) =
      ⟨a.val, a.property.1⟩ :=
  Subtype.ext (Section6.partitionIso_right U.underlying.obj A hA a)

def volumeComplementPartitionIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) :
    RVVolumeIso ((U.restrict A hA).coprod
      (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)) U := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C (volumeComplementPartitionUnderlying U A hA)
  · intro w
    rcases w.property with ⟨a, ha⟩ | ⟨b, hb⟩
    · have he : w = rvCoprodLeftMap (U.restrict A hA).underlying.obj
          (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj a :=
        Subtype.ext ha.symm
      rw [he, volumeComplementPartitionUnderlying_left]
      exact (rvCoprod_value_left (U.restrict A hA).underlying.obj
        (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj a).symm
    · have he : w = rvCoprodRightMap (U.restrict A hA).underlying.obj
          (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj b :=
        Subtype.ext hb.symm
      rw [he, volumeComplementPartitionUnderlying_right]
      exact (rvCoprod_value_right (U.restrict A hA).underlying.obj
        (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj b).symm
  · intro w
    rcases w.property with ⟨a, ha⟩ | ⟨b, hb⟩
    · have he : w = rvCoprodLeftMap (U.restrict A hA).underlying.obj
          (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj a :=
        Subtype.ext ha.symm
      rw [he, volumeComplementPartitionUnderlying_left, coprod_density_left]
      rfl
    · have he : w = rvCoprodRightMap (U.restrict A hA).underlying.obj
          (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset).underlying.obj b :=
        Subtype.ext hb.symm
      rw [he, volumeComplementPartitionUnderlying_right, coprod_density_right]
      rfl

end IntegrationInACVF.Section7
