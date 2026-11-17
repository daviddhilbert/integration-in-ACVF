module

public import Integration7.OrdinaryPointHeadIntegralRows
public import Integration7.AEOrdinaryRVVolumeHeadIntegrals
public import Integration7.AERVVolumeHeadIntegrals
public import Integration7.AERVVolumePositiveCoefficientBilinearity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual point coefficient commutes with the ordinary-input AE
head integral, through the constructed unit-family contraction chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_ordinary_point_product_head_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AEOrdinaryRVVolumeFunction hc C (n+1)) :
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C (n+1) 0
        (positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M))) f) =
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n 0 0
      (positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M)))
      (aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F =>
    apply Quotient.sound
    apply ae_rv_volume_function_equivalent_of_pointwise hc C
    intro x
    exact (ordinary_point_product_head_integral_row hc C Ξ hΞ hNames γ hγ hγ1 F.2
      (ordinaryFamilyHeadPreparation hc Ξ hGenerated F.2)
      (selectedFamilyHeadPreparation hc Ξ hGenerated
        (selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F.2)) x).trans
      (selected_volume_family_left_product_row_class hc (degreeOnePointVolumeObject (C.base : Set M))
        (F.2.headIntegral hc Ξ (ordinaryFamilyHeadPreparation hc Ξ hGenerated F.2)) x).symm
end IntegrationInACVF.Section7
