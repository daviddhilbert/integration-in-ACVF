module

public import Integration7.GammaVolumeOverlapRefinement
public import Integration7.GammaElementaryBlowupPartitions
public import Integration7.GammaVolumeCoproductRearrangements

@[expose] public section

/-! The actual volume-blowup square retains original-Gamma data on both
new steps and their endpoint isomorphism. No quotient-class permutation
is used to choose its comparison chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

set_option maxHeartbeats 2000000 in
theorem gamma_volume_blowup_diamond
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) (h : VolumeBlowup U V) (g : VolumeBlowup U W)
    (hh : h.GammaDefinable B) (hg : g.GammaDefinable B) :
    ∃ V' W', VolumeObjectGamma V' B ∧ VolumeObjectGamma W' B ∧
      ∃ (bv : VolumeBlowup V V') (bw : VolumeBlowup W W'),
        bv.GammaDefinable B ∧ bw.GammaDefinable B ∧
          ∃ e : RVVolumeIso V' W', e.GammaDefinable B := by
  let F := volumeOverlapRefinement hc C h g
  have hF := gamma_volume_overlap_refinement hc C B h g hU hh hg
  let X := h.locus.restrict F.left F.left_subset
  let X' := h.locus.restrict (h.locus.underlying.obj.domain.sdiff F.left) Set.sdiff_subset
  let Y := g.locus.restrict F.right F.right_subset
  let Y' := g.locus.restrict (g.locus.underlying.obj.domain.sdiff F.right) Set.sdiff_subset
  let hX := h.elementary.admissible.restrict F.left F.left_subset
  let hX' := h.elementary.admissible.restrict (h.locus.underlying.obj.domain.sdiff F.left) Set.sdiff_subset
  let hY := g.elementary.admissible.restrict F.right F.right_subset
  let hY' := g.elementary.admissible.restrict (g.locus.underlying.obj.domain.sdiff F.right) Set.sdiff_subset
  have hXΓ : VolumeObjectGamma X B := hh.locus.restrict F.left F.left_subset hF.left
  have hX'Γ : VolumeObjectGamma X' B := hh.locus.restrict _ Set.sdiff_subset
    ((gammaLogicInput B).sdiff hh.locus.coordinates.domain hF.left)
  have hYΓ : VolumeObjectGamma Y B := hg.locus.restrict F.right F.right_subset hF.right
  have hY'Γ : VolumeObjectGamma Y' B := hg.locus.restrict _ Set.sdiff_subset
    ((gammaLogicInput B).sdiff hg.locus.coordinates.domain hF.right)
  let CX := elementaryVolumeObject C X hX
  let CX' := elementaryVolumeObject C X' hX'
  let CY := elementaryVolumeObject C Y hY
  let CY' := elementaryVolumeObject C Y' hY'
  let E := F.exterior
  have hCX := hXΓ.elementary_canonical hc C X hX
  have hCX' := hX'Γ.elementary_canonical hc C X' hX'
  have hCY := hYΓ.elementary_canonical hc C Y hY
  have hCY' := hY'Γ.elementary_canonical hc C Y' hY'
  obtain ⟨epv,hepv⟩ := h.elementary.exists_gamma_partition_iso hc C hh.locus hh.blown hh.elementary
    F.left F.left_subset hF.left
  obtain ⟨epw,hepw⟩ := g.elementary.exists_gamma_partition_iso hc C hg.locus hg.blown hg.elementary
    F.right F.right_subset hF.right
  let ev := (h.resultOnSourceLocus hc C).trans hc C
    ((epv.symm hc C).coprod hc C F.left_remainder)
  let ew := (g.resultOnSourceLocus hc C).trans hc C
    ((epw.symm hc C).coprod hc C F.right_remainder)
  have hev : ev.GammaDefinable B := (hh.gamma_result_on_source_locus hc C).trans hc C B
    ((hepv.symm hc C B).coprod hc C B hF.left_remainder)
  have hew : ew.GammaDefinable B := (hg.gamma_result_on_source_locus hc C).trans hc C B
    ((hepw.symm hc C B).coprod hc C B hF.right_remainder)
  let evs := ev.trans hc C (volumeCoprodExchange hc C (CX.coprod CX') Y' E)
  let ews := ew.trans hc C (volumeCoprodExchange hc C (CY.coprod CY') X' E)
  have hevs : evs.GammaDefinable B := hev.trans hc C B
    (gamma_volume_coprod_exchange hc C (hCX.coprod hCX') hY'Γ hF.exterior)
  have hews : ews.GammaDefinable B := hew.trans hc C B
    (gamma_volume_coprod_exchange hc C (hCY.coprod hCY') hX'Γ hF.exterior)
  let V' := CY'.coprod ((CX.coprod CX').coprod E)
  let W' := CX'.coprod ((CY.coprod CY').coprod E)
  have hV' : VolumeObjectGamma V' B := hCY'.coprod ((hCX.coprod hCX').coprod hF.exterior)
  have hW' : VolumeObjectGamma W' B := hCX'.coprod ((hCY.coprod hCY').coprod hF.exterior)
  let bv := (VolumeBlowup.on_coprod hc C (elementaryVolumeBlowup C Y' hY') ((CX.coprod CX').coprod E)).transport
    hc C evs (RVVolumeIso.refl hc C V')
  let bw := (VolumeBlowup.on_coprod hc C (elementaryVolumeBlowup C X' hX') ((CY.coprod CY').coprod E)).transport
    hc C ews (RVVolumeIso.refl hc C W')
  have hbv : bv.GammaDefinable B := (hY'Γ.canonical_blowup hc C Y' _
    ((hCX.coprod hCX').coprod hF.exterior) hY'
    (hg.centerAlgebraic.restrict _ Set.sdiff_subset)).transport hc C evs _ hevs (hV'.identity_iso hc C)
  have hbw : bw.GammaDefinable B := (hX'Γ.canonical_blowup hc C X' _
    ((hCY.coprod hCY').coprod hF.exterior) hX'
    (hh.centerAlgebraic.restrict _ Set.sdiff_subset)).transport hc C ews _ hews (hW'.identity_iso hc C)
  obtain ⟨ec,hec⟩ := hXΓ.elementary_comparison hc C hYΓ hX hY F.overlap hF.overlap
  let first := (RVVolumeIso.refl hc C CY').coprod hc C
    ((ec.coprod hc C (RVVolumeIso.refl hc C CX')).coprod hc C (RVVolumeIso.refl hc C E))
  have hfirst : first.GammaDefinable B := (hCY'.identity_iso hc C).coprod hc C B
    ((hec.coprod hc C B (hCX'.identity_iso hc C)).coprod hc C B (hF.exterior.identity_iso hc C))
  let e := first.trans hc C (volumeCoprodReverseOuter hc C CY' CY CX' E)
  have he : e.GammaDefinable B := hfirst.trans hc C B
    (gamma_volume_coprod_reverse_outer hc C hCY' hCY hCX' hF.exterior)
  exact ⟨V',W',hV',hW',bv,bw,hbv,hbw,e,he⟩

end IntegrationInACVF.Section7
