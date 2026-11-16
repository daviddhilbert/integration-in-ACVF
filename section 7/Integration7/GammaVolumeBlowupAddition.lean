module

public import Integration7.GammaVolumeParameterGeometry
public import Integration7.GammaVolumeCoproductAssociativity
public import Integration7.GammaVolumeCoproductCharts
public import Integration7.VolumeBlowupAddition

@[expose] public section

/-! Original-Gamma common blowups are compatible with actual volume
coproducts. The added summand belongs to the complement of every center. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {k : ℕ}

def GammaVolumeObjects.coprod (U V : GammaVolumeObjects B S k) : GammaVolumeObjects B S k :=
  ⟨U.val.coprod V.val,U.property.coprod V.property⟩

theorem VolumeBlowup.GammaDefinable.coprod_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {b : VolumeBlowup U V}
    (hb : b.GammaDefinable B) (R : GammaVolumeObjects B (C.base : Set M) k) :
    (b.coprod_right hc C R.val).GammaDefinable B :=
  ⟨hb.locus,hb.complement.coprod R.property,hb.blown,hb.elementary,hb.centerAlgebraic,
    (hb.source.coprod hc C B (R.property.identity_iso hc C)).trans hc C B
      (gamma_volume_coprod_assoc hc C hb.locus hb.complement R.property),
    (hb.target.coprod hc C B (R.property.identity_iso hc C)).trans hc C B
      (gamma_volume_coprod_assoc hc C hb.blown hb.complement R.property)⟩

theorem GammaIteratedVolumeBlowup.coprod_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaIteratedVolumeBlowup B (C.base : Set M) k n U V)
    (R : GammaVolumeObjects B (C.base : Set M) k) :
    GammaIteratedVolumeBlowup B (C.base : Set M) k n (U.coprod R) (V.coprod R) := by
  induction h with
  | refl U => exact .refl _
  | @step n U V W b rest ih =>
    obtain ⟨b,hb⟩ := b
    exact .step (V := V.coprod R) ⟨b.coprod_right hc C R.val,hb.coprod_right hc C R⟩ ih

theorem GammaVolumeBlowupEquivalent.coprod_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V)
    (R : GammaVolumeObjects B (C.base : Set M) k) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k (U.coprod R) (V.coprod R) := by
  obtain ⟨m,n,U',V',hU,hV,e,he⟩ := h
  exact ⟨m,n,U'.coprod R,V'.coprod R,hU.coprod_right hc C R,hV.coprod_right hc C R,
    e.coprod hc C (RVVolumeIso.refl hc C R.val),he.coprod hc C B (R.property.identity_iso hc C)⟩

theorem GammaVolumeBlowupEquivalent.coprod_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V)
    (R : GammaVolumeObjects B (C.base : Set M) k) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k (R.coprod U) (R.coprod V) := by
  have hl : GammaVolumeBlowupEquivalent B (C.base : Set M) k (R.coprod U) (U.coprod R) :=
    .of_iso C B (volumeCoprodSwap hc C R.val U.val) (gamma_volume_coprod_swap hc C R.property U.property)
  have hr : GammaVolumeBlowupEquivalent B (C.base : Set M) k (V.coprod R) (R.coprod V) :=
    .of_iso C B (volumeCoprodSwap hc C V.val R.val) (gamma_volume_coprod_swap hc C V.property R.property)
  exact (hl.trans hc C B (h.coprod_right hc C R)).trans hc C B hr

theorem GammaVolumeBlowupEquivalent.coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' V V' : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U U')
    (g : GammaVolumeBlowupEquivalent B (C.base : Set M) k V V') :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k (U.coprod V) (U'.coprod V') :=
  (h.coprod_right hc C V).trans hc C B (g.coprod_left hc C U')

end IntegrationInACVF.Section7
