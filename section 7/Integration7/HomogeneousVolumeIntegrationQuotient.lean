module

public import Integration7.RawHomogeneousKernelRelations

@[expose] public section

/-! The actual integration quotient by the independently generated
homogeneous geometric relation ideal. Identifying this ideal with the
single basic generator remains a separate assertion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def rawHomogeneousVolumeQuotientEquiv :
    (RawRVVolumeRing hc C ⧸ rawHomogeneousVolumeRelationIdeal hc C) ≃+* RVVolumeBlowupRing hc C :=
  (Ideal.quotEquivOfEq (raw_volume_kernel_eq_homogeneous_relations hc C).symm).trans
    (rawVolumeKernelIdealQuotientEquiv hc C)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def volumeIntegrationHomogeneousKernelEquiv :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+*
      (RawRVVolumeRing hc C ⧸ rawHomogeneousVolumeRelationIdeal hc C) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact (volumeIntegrationRingEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).trans
    (rawHomogeneousVolumeQuotientEquiv hc C).symm
end IntegrationInACVF.Section7
