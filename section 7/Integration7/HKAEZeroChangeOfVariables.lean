module

public import Integration7.HKAEZeroIntegrals
public import Integration7.HKZeroFamilyChangeOfVariables

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Inverse-Jacobian change of variables for the actual weighted AE
function integral. The transform remains in coefficient degree zero. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem ae_zero_change_of_variables_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : ZeroVFVolumeFamily C (n+1) a) (B : OrdinaryVFVolumeFamily C (n+1) b)
    (f : Map F.domain B.domain) (hf : Function.Bijective f) :
    aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (Quotient.mk _ ⟨a,F⟩) =
    aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (Quotient.mk _ ⟨b,F.transport B f hf⟩) :=
  zero_family_change_of_variables_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F B f hf

end IntegrationInACVF.Section7.HK
