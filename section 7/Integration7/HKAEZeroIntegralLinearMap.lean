module

public import Integration7.HKAEZeroIntegralAddHom
public import Integration7.HKAEZeroModules
public import Integration7.HKZeroScalarRealizations
public import Integration7.HKZeroCoefficientScalarRows

@[expose] public section

/-! The genuine weighted-zero-valued AE integral preserves the actual
weighted coefficient action and is a linear map over measured zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_zero_volume_integral_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (z : RVBlowupClasses hc C 0) (f : AEZeroVolumeFunction hc C n) :
    aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (z • f) =
      z • aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      change positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C (F.2.prodZero Z).fullVFObject) = _
      rw [zero_volume_family_scalar_full_class hc F.2 Z,
        positive_volume_integration_zero_coefficient_product]
      exact (zero_volume_coefficient_smul_eq_right_product hc C _ _).symm

def aeZeroVolumeFunctionIntegralLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ) :
    AEZeroVolumeFunction hc C n →ₗ[RVBlowupClasses hc C 0] PositiveVolumeBlowupClasses hc C n where
  toAddHom := aeZeroVolumeFunctionIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  map_smul' z f := ae_zero_volume_integral_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 z f

end IntegrationInACVF.Section7.HK
