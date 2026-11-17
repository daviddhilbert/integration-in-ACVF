module

public import Integration7.GammaVolumeBlowupLoci
public import Integration7.GammaVolumeSplitComplements
public import Integration7.VolumeOverlapRefinement

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual four-piece overlap refinement retains original-Gamma
cuts, all volume charts and its exterior. The geometry is the existing
checked overlap refinement; this module tracks its full graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

structure VolumeOverlapRefinement.GammaDefinable
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {h : VolumeBlowup U V} {g : VolumeBlowup U W}
    (F : VolumeOverlapRefinement hc C h g) (B : Base (M := M)) : Prop where
  left : GammaSetDefinable B {p : Point (M := M) 0 h.locus.underlying.obj.arity | p.2 ∈ F.left.carrier}
  right : GammaSetDefinable B {p : Point (M := M) 0 g.locus.underlying.obj.arity | p.2 ∈ F.right.carrier}
  overlap : F.overlap.GammaDefinable B
  exterior : VolumeObjectGamma F.exterior B
  left_remainder : F.left_remainder.GammaDefinable B
  right_remainder : F.right_remainder.GammaDefinable B

set_option maxHeartbeats 1600000 in
theorem gamma_volume_overlap_refinement
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (P : Base (M := M))
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowup U V) (g : VolumeBlowup U W)
    (hU : VolumeObjectGamma U P) (hh : h.GammaDefinable P) (hg : g.GammaDefinable P) :
    (volumeOverlapRefinement hc C h g).GammaDefinable hc C P := by
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
  let L := gammaLogicInput P
  have hAΓ := hh.gamma_source_locus hc C
  have hBΓ := hg.gamma_source_locus hc C
  have hOΓ := L.inter hAΓ hBΓ
  have hch : ch.GammaDefinable P := (hh.gamma_source_locus_chart hc C).symm hc C P
  have hcg : cg.GammaDefinable P := (hg.gamma_source_locus_chart hc C).symm hc C P
  have hUA := hU.restrict A hA hAΓ
  have hUB := hU.restrict B hB hBΓ
  have hXΓ := gamma_volume_subobject_image ch hch O hoA hOΓ
  have hYΓ := gamma_volume_subobject_image cg hcg O hoB hOΓ
  have hex : ex.GammaDefinable P :=
    ((gamma_volume_restriction_trans_iso hc C U hU A O hA hOA hAΓ hOΓ).symm hc C P).trans hc C P
      (gamma_volume_subobject_iso hc C ch hch hUA O hoA hOΓ)
  have hey : ey.GammaDefinable P :=
    ((gamma_volume_restriction_trans_iso hc C U hU B O hB hOB hBΓ hOΓ).symm hc C P).trans hc C P
      (gamma_volume_subobject_iso hc C cg hcg hUB O hoB hOΓ)
  have hAO := L.sdiff hAΓ hOΓ
  have hBO := L.sdiff hBΓ hOΓ
  have hexrem : exrem.GammaDefinable P :=
    ((((gamma_volume_complement_image_iso hc C ch hch hUA O hoA hOΓ).symm hc C P).trans hc C P
      (gamma_volume_restriction_trans_iso hc C U hU A (A.sdiff O) hA Set.sdiff_subset hAΓ hAO)).trans hc C P
        (gamma_volume_restriction_carrier_iso hc C U hU (A.sdiff O) (A.sdiff B)
          (fun _ hx => hA hx.1) (fun _ hx => hA hx.1) hxrem hAO))
  have heyrem : eyrem.GammaDefinable P :=
    ((((gamma_volume_complement_image_iso hc C cg hcg hUB O hoB hOΓ).symm hc C P).trans hc C P
      (gamma_volume_restriction_trans_iso hc C U hU B (B.sdiff O) hB Set.sdiff_subset hBΓ hBO)).trans hc C P
        (gamma_volume_restriction_carrier_iso hc C U hU (B.sdiff O) (B.sdiff A)
          (fun _ hx => hB hx.1) (fun _ hx => hB hx.1) hyrem hBO))
  have hEΓ : VolumeObjectGamma E P := hU.restrict _ Set.sdiff_subset
    (L.sdiff hU.coordinates.domain (L.union hAΓ hBΓ))
  have heExterior : eExterior.GammaDefinable P := gamma_volume_restriction_carrier_iso hc C U hU
    (U.underlying.obj.domain.sdiff (B.union A)) (U.underlying.obj.domain.sdiff (A.union B))
    Set.sdiff_subset Set.sdiff_subset _ (L.sdiff hU.coordinates.domain (L.union hBΓ hAΓ))
  refine ⟨hXΓ,hYΓ,(hex.symm hc C P).trans hc C P hey,hEΓ,?_,?_⟩
  · exact (gamma_volume_split_complement hc C U hU A B hB hAΓ hBΓ).trans hc C P
      ((heyrem.symm hc C P).coprod hc C P (hEΓ.identity_iso hc C))
  · exact (gamma_volume_split_complement hc C U hU B A hA hBΓ hAΓ).trans hc C P
      ((hexrem.symm hc C P).coprod hc C P heExterior)

end IntegrationInACVF.Section7
