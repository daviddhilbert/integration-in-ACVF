module

public import Integration7.AEOrdinaryVolumeIntegralAddHom
public import Integration7.AEOrdinaryVolumeModules
public import Integration7.OrdinaryVolumeScalarRealizations
public import Integration7.OrdinaryVolumeCoefficientScalarRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The genuine ordinary-valued AE integral preserves the actual
ordinary coefficient action and is a linear map over RV[0]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_ordinary_rv_volume_integral_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (z : RVVolumeBlowupClasses hc C 0) (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (z • f) =
      z • aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      change positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C (F.2.prodZero Z).fullVFObject) = _
      rw [ordinary_volume_family_scalar_full_class hc F.2 Z,
        positive_volume_integration_zero_coefficient_product]
      exact (ordinary_volume_coefficient_smul_eq_right_product hc C _ _).symm

def aeOrdinaryRVVolumeFunctionIntegralLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ) :
    AEOrdinaryRVVolumeFunction hc C n →ₗ[RVVolumeBlowupClasses hc C 0] PositiveVolumeBlowupClasses hc C n where
  toAddHom := aeOrdinaryRVVolumeFunctionIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  map_smul' z f := ae_ordinary_rv_volume_integral_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 z f

end IntegrationInACVF.Section7
