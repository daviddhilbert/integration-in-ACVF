module

public import Integration7.GammaVolumeParameterGeometry
public import IntegrationSection6.GammaClosureIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Eliminating definable parameter names preserves the actual volume
objects, elementary charts, algebraic centers and common forward chains.
In particular a frozen coefficient base may be closed before applying
the VF/Gamma-generated theorems, and then descended to its original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section7

namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B D : Base (M := M)} {S : Set M} {k : ℕ}

theorem GammaDefinableBaseReduction.volumeObject
    (H : GammaDefinableBaseReduction D B) {U : PositiveRVVolumeObject (M := M) S k}
    (hU : VolumeObjectGamma U D) : VolumeObjectGamma U B :=
  ⟨H.definable hU.coordinates,H.definable hU.density⟩

def GammaDefinableBaseReduction.volumeObjects
    (H : GammaDefinableBaseReduction D B) (U : GammaVolumeObjects D S k) :
    GammaVolumeObjects B S k := ⟨U.val,H.volumeObject U.property⟩

theorem GammaDefinableBaseReduction.volumeBlowup
    (H : GammaDefinableBaseReduction D B) {U V : PositiveRVVolumeObject (M := M) S k}
    {b : VolumeBlowup U V} (hb : b.GammaDefinable D) : b.GammaDefinable B :=
  ⟨H.volumeObject hb.locus,H.volumeObject hb.complement,H.volumeObject hb.blown,
    H.definable hb.elementary,
    fun u => H.coordinate_algebraic _ _ _ (hb.centerAlgebraic u),
    H.definable hb.source,H.definable hb.target⟩

theorem GammaDefinableBaseReduction.volumeChain
    (H : GammaDefinableBaseReduction D B) {n : ℕ} {U V : GammaVolumeObjects D S k}
    (h : GammaIteratedVolumeBlowup D S k n U V) :
    GammaIteratedVolumeBlowup B S k n (H.volumeObjects U) (H.volumeObjects V) := by
  induction h with
  | refl U => exact .refl _
  | @step n U V W b rest ih =>
    obtain ⟨b,hb⟩ := b
    exact .step (V := H.volumeObjects V) ⟨b,H.volumeBlowup hb⟩ ih

theorem GammaDefinableBaseReduction.volumeCommon
    (H : GammaDefinableBaseReduction D B) {U V : GammaVolumeObjects D S k}
    (h : GammaVolumeBlowupEquivalent D S k U V) :
    GammaVolumeBlowupEquivalent B S k (H.volumeObjects U) (H.volumeObjects V) := by
  obtain ⟨m,n,U',V',hU,hV,e,he⟩ := h
  exact ⟨m,n,H.volumeObjects U',H.volumeObjects V',H.volumeChain hU,H.volumeChain hV,
    e,H.definable he⟩

end IntegrationInACVF.Section6
