module

public import Integration7.GammaVolumeBlowupEquivalence
public import Integration7.BlowupParameterExtension

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Enlarging the containing real context retains original-Gamma volume
objects, charts, center algebraicity and complete geometric chains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S T : Set M} {k n : ℕ}

theorem VolumeObjectGamma.extend {U : PositiveRVVolumeObject (M := M) S k}
    (hU : VolumeObjectGamma U B) (h : S ⊆ T) : VolumeObjectGamma (U.extend h) B :=
  ⟨hU.coordinates,hU.density⟩

theorem GammaBlowupCenter.extend {U : PositiveRVVolumeObject (M := M) S k}
    (hU : GammaBlowupCenter U B) (h : S ⊆ T) : GammaBlowupCenter (U.extend h) B :=
  fun u => hU ⟨u.val,u.property⟩

theorem RVVolumeIso.GammaDefinable.extend
    {U V : PositiveRVVolumeObject (M := M) S k} {e : RVVolumeIso U V}
    (he : e.GammaDefinable B) (h : S ⊆ T) : (e.extend h).GammaDefinable B := he

theorem VolumeBlowup.GammaDefinable.extend
    {U V : PositiveRVVolumeObject (M := M) S k} {b : VolumeBlowup U V}
    (hb : b.GammaDefinable B) (h : S ⊆ T) : (b.extend h).GammaDefinable B :=
  ⟨hb.locus.extend h,hb.complement.extend h,hb.blown.extend h,hb.elementary,
    hb.centerAlgebraic.extend h,hb.source.extend h,hb.target.extend h⟩

def GammaVolumeObjects.extend (U : GammaVolumeObjects B S k) (h : S ⊆ T) : GammaVolumeObjects B T k :=
  ⟨U.val.extend h,U.property.extend h⟩

theorem GammaIteratedVolumeBlowup.extend
    {U V : GammaVolumeObjects B S k} (b : GammaIteratedVolumeBlowup B S k n U V) (h : S ⊆ T) :
    GammaIteratedVolumeBlowup B T k n (U.extend h) (V.extend h) := by
  induction b with
  | refl U => exact .refl _
  | @step n U V W b rest ih =>
    obtain ⟨b,hb⟩ := b
    exact .step (V := V.extend h) ⟨b.extend h,hb.extend h⟩ ih

theorem GammaVolumeBlowupEquivalent.extend
    {U V : GammaVolumeObjects B S k} (b : GammaVolumeBlowupEquivalent B S k U V) (h : S ⊆ T) :
    GammaVolumeBlowupEquivalent B T k (U.extend h) (V.extend h) := by
  obtain ⟨m,n,U',V',hU,hV,e,he⟩ := b
  exact ⟨m,n,U'.extend h,V'.extend h,hU.extend h,hV.extend h,e.extend h,he.extend h⟩

end IntegrationInACVF.Section7
