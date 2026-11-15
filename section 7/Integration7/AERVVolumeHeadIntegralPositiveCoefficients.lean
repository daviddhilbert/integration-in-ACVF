import Integration7.FrozenHeadIntegralPositiveCoefficients
import Integration7.AERVVolumeHeadIntegralAdditivity

/-! The actual positive homogeneous head integral commutes with every
positive RV coefficient on almost-everywhere function classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}

theorem ae_rv_volume_head_integral_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C (n+1) k) :
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeFunctionPositiveCoefficientProduct hc C (n+1) p k u f) =
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p (k+1) u
      (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      exact (selected_head_integral_positive_coefficient_row_class hc C Ξ hΞ hNames γ hγ hγ1 F.2 U
        (selectedFamilyHeadPreparation hc Ξ hGenerated F.2)
        (selectedFamilyHeadPreparation hc Ξ hGenerated (selectedVolumeFamilyLeftProduct U F.2)) x).trans
        (selected_volume_family_left_product_row_class hc U
          (F.2.headIntegral hc Ξ (selectedFamilyHeadPreparation hc Ξ hGenerated F.2)) x).symm
end IntegrationInACVF.Section7
