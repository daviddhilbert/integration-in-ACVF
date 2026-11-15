import Integration7.PositiveCoefficientAppendedIntegrals
import Integration7.AERVVolumePositiveCoefficientProducts

/-! Positive-coefficient compatibility of the actual appended integral
on the existing almost-everywhere volume-function quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}

theorem ae_rv_volume_appended_integral_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C n k) :
    HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f))
      (rvVolumeBlowupClassesProduct hc C (p+1) (appendVolumeDegree (n+1) k+1) u
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)) :=
  Quotient.inductionOn₂ u f (fun U F =>
    selected_family_appended_integral_positive_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U F.2)

end IntegrationInACVF.Section7
