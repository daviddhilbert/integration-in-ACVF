module

public import Integration7.HKFrozenHeadWeightedZeroCoefficients
public import Integration7.HKAERVWeightedZeroModules
public import Integration7.AERVVolumeHeadIntegralAdditivity

@[expose] public section

/-! The genuine positive-valued AE head map is linear over the full weighted measured-zero coefficient semiring before normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_rv_volume_head_integral_weighted_zero_smul
    (z : RVBlowupClasses hc C 0) (f : AERVVolumeFunction hc C (n+1) k) :
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (z • f) =
      z • aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      exact (selected_head_integral_weighted_zero_coefficient_row_class hc C Ξ hΞ hNames γ hγ hγ1 F.2 Z
        (selectedFamilyHeadPreparation hc Ξ hGenerated F.2)
        (selectedFamilyHeadPreparation hc Ξ hGenerated (selectedFamilyWeightedZeroProduct F.2 Z)) x).trans
        (selected_family_weighted_zero_row_scalar hc
          (F.2.headIntegral hc Ξ (selectedFamilyHeadPreparation hc Ξ hGenerated F.2)) Z x).symm

def aeRVVolumeHeadIntegralWeightedZeroLinearMap (n k : ℕ) :
    AERVVolumeFunction hc C (n+1) k →ₗ[RVBlowupClasses hc C 0] AERVVolumeFunction hc C n (k+1) where
  toAddHom := aeRVVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
  map_smul' := ae_rv_volume_head_integral_weighted_zero_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1
end IntegrationInACVF.Section7.HK
