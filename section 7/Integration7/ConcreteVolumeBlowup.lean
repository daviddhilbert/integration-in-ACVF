import Integration7.VolumePartition
import Integration7.VolumeBlowupTransport
import Integration7.ElementaryBlowupRestriction
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7.VolumeBlowup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def via_locus (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    {P Q : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso P (U.restrict A hA)) (b : ElementaryBlowup P Q) :
    VolumeBlowup U (Q.coprod (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)) where
  locus := P
  complement := U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset
  blownLocus := Q
  elementary := b
  sourceIso := ((volumeComplementPartitionIso hc C U A hA).symm hc C).trans hc C
    ((f.symm hc C).coprod hc C (RVVolumeIso.refl hc C _))
  targetIso := RVVolumeIso.refl hc C _

def along_locus (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    {Q : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup (U.restrict A hA) Q) :
    VolumeBlowup U (Q.coprod (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)) :=
  via_locus hc C U A hA (RVVolumeIso.refl hc C _) b
end IntegrationInACVF.Section7.VolumeBlowup
