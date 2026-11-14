import Integration7.VolumeBlowupEquivalence
import Integration7.VolumeCoproductAssociativity

/-! Compatibility of the actual common-blowup relation with definable
coproducts. The blown locus stays fixed and the added summand is included
in its complement. This proves the positive additive part of Lemma 7.4. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VolumeBlowup.coprod_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : VolumeBlowup U V) (R : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VolumeBlowup (U.coprod R) (V.coprod R) where
  locus := b.locus
  complement := b.complement.coprod R
  blownLocus := b.blownLocus
  elementary := b.elementary
  sourceIso := (b.sourceIso.coprod hc C (RVVolumeIso.refl hc C R)).trans hc C
    (volumeCoprodAssoc hc C b.locus b.complement R)
  targetIso := (b.targetIso.coprod hc C (RVVolumeIso.refl hc C R)).trans hc C
    (volumeCoprodAssoc hc C b.blownLocus b.complement R)

theorem IteratedVolumeBlowup.coprod_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {n : ℕ}
    (h : IteratedVolumeBlowup n U V) (R : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    IteratedVolumeBlowup n (U.coprod R) (V.coprod R) := by
  induction h with
  | refl U => exact .refl _
  | step b h ih =>
    obtain ⟨b⟩ := b
    exact .step ⟨b.coprod_right hc C R⟩ ih

theorem VolumeBlowupEquivalent.coprod_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (R : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VolumeBlowupEquivalent (U.coprod R) (V.coprod R) := by
  obtain ⟨m, n, U', V', hU, hV, ⟨e⟩⟩ := h
  exact ⟨m, n, U'.coprod R, V'.coprod R, hU.coprod_right hc C R, hV.coprod_right hc C R,
    ⟨e.coprod hc C (RVVolumeIso.refl hc C R)⟩⟩

theorem VolumeBlowupEquivalent.coprod_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (R : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VolumeBlowupEquivalent (R.coprod U) (R.coprod V) :=
  ((VolumeBlowupEquivalent.of_iso C (volumeCoprodSwap hc C R U)).trans hc C
    (h.coprod_right hc C R)).trans hc C
      (VolumeBlowupEquivalent.of_iso C (volumeCoprodSwap hc C V R))

theorem VolumeBlowupEquivalent.coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' V V' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U U') (g : VolumeBlowupEquivalent V V') :
    VolumeBlowupEquivalent (U.coprod V) (U'.coprod V') :=
  (h.coprod_right hc C V).trans hc C (g.coprod_left hc C U')

end IntegrationInACVF.Section7
