import Integration7.VolumeComplementImages
import Integration7.VolumeCoproductComplements
import Integration7.IteratedVolumeBlowups

/-! Every coproduct presentation of a blowup has a genuine definable
source locus, a chart on that locus, and the corresponding complement. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.VolumeBlowup

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : VolumeBlowup U W)

def sourceLocus : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M) :=
  volumeSubobjectImage (b.sourceIso.symm hc C) (coprodEssentialLeftMap b.locus b.complement).image (by
    rintro x ⟨u, rfl⟩
    exact (coprodEssentialLeftMap b.locus b.complement u).property)

theorem sourceLocus_subset_essential : (b.sourceLocus hc C).carrier ⊆ U.essential.obj.domain.carrier :=
  volumeSubobjectImage_subset _ _ _

theorem sourceLocus_subset : (b.sourceLocus hc C).carrier ⊆ U.underlying.obj.domain.carrier :=
  (b.sourceLocus_subset_essential hc C).trans (rvEssentialLabels_subset U.underlying.obj)

def sourceLocusChart : RVVolumeIso b.locus (U.restrict (b.sourceLocus hc C) (b.sourceLocus_subset hc C)) := by
  let A := (coprodEssentialLeftMap b.locus b.complement).image
  have hA : A.carrier ⊆ (b.locus.coprod b.complement).essential.obj.domain.carrier := by
    rintro x ⟨u, rfl⟩
    exact (coprodEssentialLeftMap b.locus b.complement u).property
  exact (volumeCoprodLeftImageIso hc C b.locus b.complement).trans hc C
    ((b.sourceIso.symm hc C).subobjectImage hc C A hA)

def sourceComplementIso :
    RVVolumeIso (U.restrict (U.underlying.obj.domain.sdiff (b.sourceLocus hc C)) Set.sdiff_subset) b.complement := by
  let A := (coprodEssentialLeftMap b.locus b.complement).image
  have hA : A.carrier ⊆ (b.locus.coprod b.complement).essential.obj.domain.carrier := by
    rintro x ⟨u, rfl⟩
    exact (coprodEssentialLeftMap b.locus b.complement u).property
  exact (((b.sourceIso.symm hc C).complementImage hc C A hA).symm hc C).trans hc C
    (volumeCoprodLeftComplementIso hc C b.locus b.complement)

def resultOnSourceLocus :
    RVVolumeIso W (b.blownLocus.coprod
      (U.restrict (U.underlying.obj.domain.sdiff (b.sourceLocus hc C)) Set.sdiff_subset)) :=
  b.targetIso.trans hc C ((RVVolumeIso.refl hc C b.blownLocus).coprod hc C
    ((b.sourceComplementIso hc C).symm hc C))

end IntegrationInACVF.Section7.VolumeBlowup
