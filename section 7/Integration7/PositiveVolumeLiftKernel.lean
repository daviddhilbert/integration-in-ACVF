module

public import Integration7.RVVolumeLiftCommonContextKernel
public import Integration7.CommonContextVolumeDescent
public import Integration7.VolumeBlowupLiftInvariance

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Proposition 7.8 in every positive degree on the original volume
objects and original real base. Common forward volume blowups are
equivalent to an actual almost-everywhere volume isomorphism of lifts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem common_volume_blowup_of_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) : VolumeBlowupEquivalent U V :=
  ((rv_volume_lift_common_context_kernel hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U V f).descend hc C hNames).toOrdinary
    hc C (⟨(C.base : Set M),Ξ⟩ : Base (M := M))

theorem proposition_7_8
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    Nonempty (VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) ↔ VolumeBlowupEquivalent U V := by
  constructor
  · rintro ⟨f⟩
    exact common_volume_blowup_of_lift_iso hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U V f
  · intro h
    exact h.nonempty_volume_lift_iso hc C Ξ hGenerated

end IntegrationInACVF.Section7
