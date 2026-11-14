import Integration7.VolumeBlowupLoci
import Integration7.VolumeComplementPartitions
import Integration7.VolumeRestrictionIdentifications

/-! The intersection, the two differences and the exterior give an actual
four-part refinement of two volume-blowup loci over their original base. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

structure VolumeOverlapRefinement (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowup U V) (g : VolumeBlowup U W) where
  left : DefSet (rawRVSpace (M := M) h.locus.underlying.obj.arity) (C.base : Set M)
  left_subset : left.carrier ⊆ h.locus.underlying.obj.domain.carrier
  right : DefSet (rawRVSpace (M := M) g.locus.underlying.obj.arity) (C.base : Set M)
  right_subset : right.carrier ⊆ g.locus.underlying.obj.domain.carrier
  overlap : RVVolumeIso (h.locus.restrict left left_subset) (g.locus.restrict right right_subset)
  exterior : PositiveRVVolumeObject (M := M) (C.base : Set M) k
  left_remainder : RVVolumeIso
    (U.restrict (U.underlying.obj.domain.sdiff (h.sourceLocus hc C)) Set.sdiff_subset)
    ((g.locus.restrict (g.locus.underlying.obj.domain.sdiff right) Set.sdiff_subset).coprod exterior)
  right_remainder : RVVolumeIso
    (U.restrict (U.underlying.obj.domain.sdiff (g.sourceLocus hc C)) Set.sdiff_subset)
    ((h.locus.restrict (h.locus.underlying.obj.domain.sdiff left) Set.sdiff_subset).coprod exterior)

def volumeOverlapRefinement (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowup U V) (g : VolumeBlowup U W) : VolumeOverlapRefinement hc C h g := by
  let A := h.sourceLocus hc C
  let B := g.sourceLocus hc C
  let hA := h.sourceLocus_subset hc C
  let hB := g.sourceLocus_subset hc C
  let O := A.inter B
  have hOA : O.carrier ⊆ A.carrier := fun _ hx => hx.1
  have hOB : O.carrier ⊆ B.carrier := fun _ hx => hx.2
  have hoA : O.carrier ⊆ (U.restrict A hA).essential.obj.domain.carrier := by
    intro x hx
    exact (mem_rvEssentialLabels (U.restrict A hA).underlying.obj ⟨x, hx.1⟩).mpr
      (U.essential_nonzero ⟨x, h.sourceLocus_subset_essential hc C hx.1⟩)
  have hoB : O.carrier ⊆ (U.restrict B hB).essential.obj.domain.carrier := by
    intro x hx
    exact (mem_rvEssentialLabels (U.restrict B hB).underlying.obj ⟨x, hx.2⟩).mpr
      (U.essential_nonzero ⟨x, g.sourceLocus_subset_essential hc C hx.2⟩)
  let ch := (h.sourceLocusChart hc C).symm hc C
  let cg := (g.sourceLocusChart hc C).symm hc C
  let X := volumeSubobjectImage ch O hoA
  let Y := volumeSubobjectImage cg O hoB
  let hX := (volumeSubobjectImage_subset ch O hoA).trans (rvEssentialLabels_subset h.locus.underlying.obj)
  let hY := (volumeSubobjectImage_subset cg O hoB).trans (rvEssentialLabels_subset g.locus.underlying.obj)
  let ex := ((volumeRestrictionTransIso hc C U A O hA hOA).symm hc C).trans hc C
    (ch.subobjectImage hc C O hoA)
  let ey := ((volumeRestrictionTransIso hc C U B O hB hOB).symm hc C).trans hc C
    (cg.subobjectImage hc C O hoB)
  have hxrem : (A.sdiff O).carrier = (A.sdiff B).carrier := by
    ext x
    constructor
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun hb => hn ⟨ha, hb⟩⟩
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun hab => hn hab.2⟩
  have hyrem : (B.sdiff O).carrier = (B.sdiff A).carrier := by
    ext x
    constructor
    · rintro ⟨hb, hn⟩
      exact ⟨hb, fun ha => hn ⟨ha, hb⟩⟩
    · rintro ⟨hb, hn⟩
      exact ⟨hb, fun hab => hn hab.1⟩
  let exrem := (((ch.complementImage hc C O hoA).symm hc C).trans hc C
    (volumeRestrictionTransIso hc C U A (A.sdiff O) hA Set.sdiff_subset)).trans hc C
      (volumeRestrictionCarrierIso hc C U (A.sdiff O) (A.sdiff B)
        (fun _ hx => hA hx.1) (fun _ hx => hA hx.1) hxrem)
  let eyrem := (((cg.complementImage hc C O hoB).symm hc C).trans hc C
    (volumeRestrictionTransIso hc C U B (B.sdiff O) hB Set.sdiff_subset)).trans hc C
      (volumeRestrictionCarrierIso hc C U (B.sdiff O) (B.sdiff A)
        (fun _ hx => hB hx.1) (fun _ hx => hB hx.1) hyrem)
  let E := U.restrict (U.underlying.obj.domain.sdiff (A.union B)) Set.sdiff_subset
  let eExterior := volumeRestrictionCarrierIso hc C U
    (U.underlying.obj.domain.sdiff (B.union A)) (U.underlying.obj.domain.sdiff (A.union B))
    Set.sdiff_subset Set.sdiff_subset
    (congrArg (fun D => U.underlying.obj.domain.carrier \ D) (Set.union_comm B.carrier A.carrier))
  exact {
    left := X
    left_subset := hX
    right := Y
    right_subset := hY
    overlap := (ex.symm hc C).trans hc C ey
    exterior := E
    left_remainder := (volumeSplitComplement hc C U A B hB).trans hc C
      ((eyrem.symm hc C).coprod hc C (RVVolumeIso.refl hc C E))
    right_remainder := (volumeSplitComplement hc C U B A hA).trans hc C
      ((exrem.symm hc C).coprod hc C eExterior) }

end IntegrationInACVF.Section7
