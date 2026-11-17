module

public import Integration7.AERVVolumeOrdinaryCoefficientModules
public import Integration7.VolumeFunctionZeroCoefficientIntegrals
public import Integration7.AERVVolumeFunctionIntegralAddHom

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual canonical integral is linear over the ordinary RV[0]
coefficient semiring on every positive homogeneous function space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def aeRVVolumeFunctionIntegralOrdinaryLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n k : ℕ) :
    AERVVolumeFunction hc C n k →ₗ[RVVolumeBlowupClasses hc C 0]
      PositiveVolumeBlowupClasses hc C ((k+1)+n) where
  toAddHom := aeRVVolumeFunctionIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
  map_smul' z f := (ae_rv_volume_function_integral_zero_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f z).trans
    (ordinary_volume_coefficient_smul_eq_right_product hc C z _).symm

end IntegrationInACVF.Section7
