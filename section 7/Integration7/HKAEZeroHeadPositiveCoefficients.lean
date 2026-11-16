module

public import Integration7.HKFrozenZeroPositiveCoefficientProducts
public import Integration7.HKAEZeroHeadIntegrals
public import Integration7.HKAEZeroPositiveCoefficientProducts
public import Integration7.AERVVolumeHeadIntegrals
public import Integration7.AERVVolumePositiveCoefficientBilinearity

@[expose] public section

/-! Every actual positive coefficient commutes with the weighted-zero-input AE head integral through the constructed density-preserving contraction chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}

theorem ae_zero_head_integral_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AEZeroVolumeFunction hc C (n+1)) :
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeZeroVolumeFunctionPositiveCoefficientProduct hc C (n+1) p u f) =
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p 0 u
      (aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      exact (zero_head_integral_positive_coefficient_row_class hc C Ξ hΞ hNames γ hγ hγ1 F.2 U
        (zeroFamilyHeadPreparation hc Ξ hGenerated F.2)
        (selectedFamilyHeadPreparation hc Ξ hGenerated (selectedZeroFamilyPositiveProduct U F.2)) x).trans
        (selected_volume_family_left_product_row_class hc U
          (F.2.headIntegral hc Ξ (zeroFamilyHeadPreparation hc Ξ hGenerated F.2)) x).symm
end IntegrationInACVF.Section7.HK
