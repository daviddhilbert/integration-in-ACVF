module

public import Integration7.AEOrdinaryVolumeRealizationClasses
public import Integration7.PositiveVolumeIntegrationEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual integration of ordinary degree-zero-valued AE functions,
using their unit-density VF realization and the checked volume integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def aeOrdinaryRVVolumeFunctionIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    AEOrdinaryRVVolumeFunction hc C n → PositiveVolumeBlowupClasses hc C n :=
  fun f => positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (aeOrdinaryRVVolumeFunctionRealizationClass hc C n f)

@[simp] theorem aeOrdinaryRVVolumeFunctionIntegral_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVolumeFunctionPresentation C (n+1)) :
    aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ F) =
      positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C F.2.fullVFObject) := rfl

end IntegrationInACVF.Section7
