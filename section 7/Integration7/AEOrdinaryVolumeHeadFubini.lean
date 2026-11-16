module

public import Integration7.AEOrdinaryRVVolumeHeadIntegrals
public import Integration7.OrdinaryVolumeFamilyHeadFubini
public import Integration7.AppendedVolumeFunctionIntegrals

@[expose] public section

/-! Ordinary-valued AE functions satisfy first-head Fubini on their actual
quotient. The only heterogeneous equality is the arithmetic total degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_ordinary_rv_volume_function_appended_head_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AEOrdinaryRVVolumeFunction hc C (n+1)) :
    HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f))
      (aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F =>
    exact ordinary_family_appended_head_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2
      (ordinaryFamilyHeadPreparation hc Ξ hGenerated F.2)

end IntegrationInACVF.Section7
