import Integration7.ElementaryVolumeLiftInvariance
import Integration7.FixedVFVolumeCoproductIsomorphisms
import Integration7.VolumeLiftCoproductBijections

/-! Elementary blowups on arbitrary definable loci, their finite
iterations and common forward volume blowups have isomorphic VF lifts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem VolumeBlowup.nonempty_volume_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : VolumeBlowup U V) :
    Nonempty (VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) := by
  obtain ⟨e⟩ := b.elementary.nonempty_volume_lift_iso hc C Ξ hGenerated
  obtain ⟨s⟩ := b.sourceIso.nonempty_full_lift_iso hc C Ξ hGenerated
  obtain ⟨t⟩ := b.targetIso.nonempty_full_lift_iso hc C Ξ hGenerated
  let f := e.coprod hc C (VFVolumeIso.refl hc C (rvVolumeLift b.complement))
  exact ⟨s.trans hc C (((volumeLiftCoprodIso hc C b.locus b.complement).symm hc C).trans hc C
    (f.trans hc C ((volumeLiftCoprodIso hc C b.blownLocus b.complement).trans hc C (t.symm hc C))))⟩

theorem IteratedVolumeBlowup.nonempty_volume_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    {m : ℕ} {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : IteratedVolumeBlowup m U V) :
    Nonempty (VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) := by
  induction h with
  | refl U => exact ⟨VFVolumeIso.refl hc C (rvVolumeLift U)⟩
  | step hb h ih =>
    obtain ⟨b⟩ := hb
    obtain ⟨f⟩ := b.nonempty_volume_lift_iso hc C Ξ hGenerated
    obtain ⟨g⟩ := ih
    exact ⟨f.trans hc C g⟩

theorem VolumeBlowupEquivalent.nonempty_volume_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) :
    Nonempty (VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) := by
  obtain ⟨m,n,P,Q,hP,hQ,⟨e⟩⟩ := h
  obtain ⟨f⟩ := hP.nonempty_volume_lift_iso hc C Ξ hGenerated
  obtain ⟨g⟩ := hQ.nonempty_volume_lift_iso hc C Ξ hGenerated
  obtain ⟨j⟩ := e.nonempty_full_lift_iso hc C Ξ hGenerated
  exact ⟨f.trans hc C (j.trans hc C (g.symm hc C))⟩

end IntegrationInACVF.Section7
