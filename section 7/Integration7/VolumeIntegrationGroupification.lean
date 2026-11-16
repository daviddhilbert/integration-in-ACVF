module

public import Integration7.VolumeIntegrationSemiringEquivalence
public import Integration7.SemiringGroupificationDifferences

@[expose] public section

/-! The proved integration semiring equivalence induces the canonical
ring equivalence on universal groupifications. Identification of the RV
kernel with the degree-one principal relation is a separate step of7.13. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

abbrev VFVolumeRing : Type := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact SemiringGroupification (VFVolumeSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

abbrev RVVolumeBlowupRing := SemiringGroupification (RVVolumeBlowupSemiring hc C)

def volumeIntegrationRingEquiv :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+* RVVolumeBlowupRing hc C := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact semiringGroupificationEquiv (volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

theorem volume_integration_ring_of
    (a : VFVolumeSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1) :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    volumeIntegrationRingEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (semiringGroupificationOf _ a) =
      semiringGroupificationOf _ (volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact semiringGroupificationEquiv_of (volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1) a

end IntegrationInACVF.Section7
