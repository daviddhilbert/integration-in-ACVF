import Integration7.HKVolumeComponentIntegralWeightedLinearity
import Integration7.HKGradedAEVolumeActionCoherence
import Integration7.HKZeroPositiveCoefficientIntegrals
import Integration7.AERVPositiveCoefficientAppendedIntegrals

/-! In every homogeneous degree, including ordinary values and ordinary
coefficients, integration preserves the actual graded coefficient action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ae_volume_component_integral_coefficient_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n i j : ℕ)
    (u : RVBlowupClasses hc C i) (f : AEVolumeFunctionComponent hc C n j) :
    HEq (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (i+j)
      (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f))
      (rvVolumeBlowupClassesProduct hc C i ((n+j)+1) u
        (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f)) := by
  cases i with
  | zero =>
    have h := ae_volume_component_integral_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n := n) (Nat.zero_add j)
      (ae_volume_component_zero_coefficient_heq hc C n j u f)
    have hScalar := (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j).map_smul u f
    exact h.trans ((heq_of_eq hScalar).trans (rv_volume_zero_product_smul_heq hc C _ u _).symm)
  | succ p =>
    cases j with
    | zero =>
      exact (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n p
        (aeZeroVolumeFunctionPositiveCoefficientProduct hc C n p u f)).trans
          (ae_zero_positive_coefficient_appended_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 u f)
    | succ k =>
      have hOutput := ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n ((p+1)+k)
        (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f)
      have hProduct := ae_rv_volume_appended_integral_positive_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 u f
      have hDegree : appendVolumeDegree (n+1) k+1=(n+(k+1))+1 := by rw [append_volume_degree_eq]; omega
      have hInput := rv_volume_product_heq_of_inputs hc C (rfl : p+1=p+1) hDegree (HEq.rfl : HEq u u)
        (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f).symm
      exact hOutput.trans (hProduct.trans hInput)

end IntegrationInACVF.Section7.HK
