module

public import Integration7.HKFrozenZeroWeightedScalarIntegrals
public import Integration7.HKAEZeroHeadIntegralAdditivity
public import Integration7.HKAEZeroModules
public import Integration7.HKAERVHeadWeightedZeroLinearity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual zero-valued AE head integral is linear over arbitrary weighted measured-zero coefficients, by its genuine finite-factor fibre computation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_zero_head_integral_weighted_smul
    (z : RVBlowupClasses hc C 0) (f : AEZeroVolumeFunction hc C (n+1)) :
    aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (z • f) =
      z • aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      exact (zero_head_integral_weighted_coefficient_row_class hc C Ξ hΞ hNames γ hγ hγ1 F.2 Z
        (zeroFamilyHeadPreparation hc Ξ hGenerated F.2)
        (zeroFamilyHeadPreparation hc Ξ hGenerated (F.2.prodZero Z)) x).trans
        (selected_family_weighted_zero_row_scalar hc
          (F.2.headIntegral hc Ξ (zeroFamilyHeadPreparation hc Ξ hGenerated F.2)) Z x).symm

def aeZeroVolumeHeadIntegralWeightedLinearMap (n : ℕ) :
    AEZeroVolumeFunction hc C (n+1) →ₗ[RVBlowupClasses hc C 0] AERVVolumeFunction hc C n 0 where
  toAddHom := aeZeroVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  map_smul' := ae_zero_head_integral_weighted_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1
end IntegrationInACVF.Section7.HK
