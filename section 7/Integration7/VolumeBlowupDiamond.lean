import Integration7.VolumeOverlapRefinement
import Integration7.ElementaryBlowupPartitions
import Integration7.VolumeBlowupTransport
import Integration7.VolumeIsomorphismClasses

/-! Two actual volume blowups admit one further blowup on each branch,
with volume-isomorphic endpoints. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem volumeBlowup_diamond (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowup U V) (g : VolumeBlowup U W) :
    ∃ V' W', Nonempty (VolumeBlowup V V') ∧ Nonempty (VolumeBlowup W W') ∧ Nonempty (RVVolumeIso V' W') := by
  let F := volumeOverlapRefinement hc C h g
  let X := h.locus.restrict F.left F.left_subset
  let X' := h.locus.restrict (h.locus.underlying.obj.domain.sdiff F.left) Set.sdiff_subset
  let Y := g.locus.restrict F.right F.right_subset
  let Y' := g.locus.restrict (g.locus.underlying.obj.domain.sdiff F.right) Set.sdiff_subset
  let hX := h.elementary.admissible.restrict F.left F.left_subset
  let hX' := h.elementary.admissible.restrict (h.locus.underlying.obj.domain.sdiff F.left) Set.sdiff_subset
  let hY := g.elementary.admissible.restrict F.right F.right_subset
  let hY' := g.elementary.admissible.restrict (g.locus.underlying.obj.domain.sdiff F.right) Set.sdiff_subset
  let CX := elementaryVolumeObject C X hX
  let CX' := elementaryVolumeObject C X' hX'
  let CY := elementaryVolumeObject C Y hY
  let CY' := elementaryVolumeObject C Y' hY'
  let E := F.exterior
  let ev : RVVolumeIso V ((CX.coprod CX').coprod (Y'.coprod E)) :=
    (h.resultOnSourceLocus hc C).trans hc C
      (((h.elementary.partitionIso hc C F.left F.left_subset).symm hc C).coprod hc C F.left_remainder)
  let ew : RVVolumeIso W ((CY.coprod CY').coprod (X'.coprod E)) :=
    (g.resultOnSourceLocus hc C).trans hc C
      (((g.elementary.partitionIso hc C F.right F.right_subset).symm hc C).coprod hc C F.right_remainder)
  have evsplit : Nonempty (RVVolumeIso V (Y'.coprod ((CX.coprod CX').coprod E))) := by
    apply (positiveVolumeIsoClass_eq_iff hc C).mp
    rw [positiveVolumeIsoClass_iso hc C ev]
    simp only [positiveVolumeIsoClass_coprod]
    abel
  have ewsplit : Nonempty (RVVolumeIso W (X'.coprod ((CY.coprod CY').coprod E))) := by
    apply (positiveVolumeIsoClass_eq_iff hc C).mp
    rw [positiveVolumeIsoClass_iso hc C ew]
    simp only [positiveVolumeIsoClass_coprod]
    abel
  obtain ⟨evs⟩ := evsplit
  obtain ⟨ews⟩ := ewsplit
  let V' := CY'.coprod ((CX.coprod CX').coprod E)
  let W' := CX'.coprod ((CY.coprod CY').coprod E)
  let bv := VolumeBlowup.on_coprod hc C (elementaryVolumeBlowup C Y' hY') ((CX.coprod CX').coprod E)
  let bw := VolumeBlowup.on_coprod hc C (elementaryVolumeBlowup C X' hX') ((CY.coprod CY').coprod E)
  let ec := elementaryBlowupIso hc C F.overlap (elementaryVolumeBlowup C X hX) (elementaryVolumeBlowup C Y hY)
  refine ⟨V', W', ⟨bv.transport_source hc C evs⟩, ⟨bw.transport_source hc C ews⟩, ?_⟩
  apply (positiveVolumeIsoClass_eq_iff hc C).mp
  change positiveVolumeIsoClass hc C (CY'.coprod ((CX.coprod CX').coprod E)) =
    positiveVolumeIsoClass hc C (CX'.coprod ((CY.coprod CY').coprod E))
  simp only [positiveVolumeIsoClass_coprod]
  rw [positiveVolumeIsoClass_iso hc C ec]
  abel

end IntegrationInACVF.Section7
