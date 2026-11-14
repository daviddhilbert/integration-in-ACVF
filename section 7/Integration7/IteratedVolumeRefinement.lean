import Integration7.VolumeBlowupDiamond
import IntegrationSection6.Iteration

/-! The actual volume-blowup diamond supplies the hypothesis of the
previously proved finite-grid argument. All step counts are retained. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def volumeClassBlowup (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ)
    (a b : PositiveVolumeIsoClasses hc C k) : Prop :=
  ∃ U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k,
    positiveVolumeIsoClass hc C U = a ∧ positiveVolumeIsoClass hc C V = b ∧ Nonempty (VolumeBlowup U V)

theorem volumeClassBlowup_diamond
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Section6.Iteration.Diamond (volumeClassBlowup hc C k) := by
  intro a b c hab hac
  obtain ⟨U, V, hU, hV, ⟨h⟩⟩ := hab
  obtain ⟨T, W, hT, hW, ⟨g⟩⟩ := hac
  obtain ⟨e⟩ := (positiveVolumeIsoClass_eq_iff hc C).mp (hU.trans hT.symm)
  obtain ⟨V', W', hV', hW', ⟨f⟩⟩ := volumeBlowup_diamond hc C h (g.transport_source hc C e)
  exact ⟨positiveVolumeIsoClass hc C V', ⟨V, V', hV, rfl, hV'⟩,
    ⟨W, W', hW, (positiveVolumeIsoClass_iso hc C f).symm, hW'⟩⟩

theorem IteratedVolumeBlowup.classSteps
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k n : ℕ} {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : IteratedVolumeBlowup n U V) :
    Section6.Iteration.Steps (volumeClassBlowup hc C k) n
      (positiveVolumeIsoClass hc C U) (positiveVolumeIsoClass hc C V) := by
  induction h with
  | refl U => exact .refl _
  | step b rest ih => exact .cons ⟨_, _, rfl, rfl, b⟩ ih

theorem iteratedVolumeBlowup_of_classSteps
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k n : ℕ} {a b : PositiveVolumeIsoClasses hc C k}
    (h : Section6.Iteration.Steps (volumeClassBlowup hc C k) n a b)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : positiveVolumeIsoClass hc C U = a) :
    ∃ V, IteratedVolumeBlowup n U V ∧ positiveVolumeIsoClass hc C V = b := by
  induction h generalizing U with
  | refl => exact ⟨U, .refl U, hU⟩
  | cons h rest ih =>
    obtain ⟨X, Y, hX, hY, ⟨bXY⟩⟩ := h
    obtain ⟨e⟩ := (positiveVolumeIsoClass_eq_iff hc C).mp (hU.trans hX.symm)
    obtain ⟨V, hV, hv⟩ := ih hY
    exact ⟨V, .step ⟨bXY.transport_source hc C e⟩ hV, hv⟩

theorem IteratedVolumeBlowup.common_refinement_of_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k m n : ℕ} {U U' V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U U') (h : IteratedVolumeBlowup m U V) (g : IteratedVolumeBlowup n U' W) :
    ∃ V' W', IteratedVolumeBlowup n V V' ∧ IteratedVolumeBlowup m W W' ∧ Nonempty (RVVolumeIso V' W') := by
  have hg : Section6.Iteration.Steps (volumeClassBlowup hc C k) n
      (positiveVolumeIsoClass hc C U) (positiveVolumeIsoClass hc C W) := by
    rw [positiveVolumeIsoClass_iso hc C f]
    exact g.classSteps hc C
  obtain ⟨a, hva, hwa⟩ := Section6.Iteration.grid (volumeClassBlowup_diamond hc C k) (h.classSteps hc C) hg
  obtain ⟨V', hV', hv⟩ := iteratedVolumeBlowup_of_classSteps hc C hva rfl
  obtain ⟨W', hW', hw⟩ := iteratedVolumeBlowup_of_classSteps hc C hwa rfl
  exact ⟨V', W', hV', hW', (positiveVolumeIsoClass_eq_iff hc C).mp (hv.trans hw.symm)⟩

theorem IteratedVolumeBlowup.common_refinement
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k m n : ℕ} {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : IteratedVolumeBlowup m U V) (g : IteratedVolumeBlowup n U W) :
    ∃ V' W', IteratedVolumeBlowup n V V' ∧ IteratedVolumeBlowup m W W' ∧ Nonempty (RVVolumeIso V' W') :=
  h.common_refinement_of_iso hc C (RVVolumeIso.refl hc C U) g

end IntegrationInACVF.Section7
