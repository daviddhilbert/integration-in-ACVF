import Integration7.FrozenOrdinaryScalarIntegrals
import Integration7.AEOrdinaryHeadIntegralAdditivity
import Integration7.AERVVolumeHeadOrdinaryLinearity

/-! The actual ordinary-input head integral is linear over ordinary
RV[0] coefficients, through its genuine finite-factor fibre computation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_ordinary_head_integral_ordinary_smul
    (z : RVVolumeBlowupClasses hc C 0) (f : AEOrdinaryRVVolumeFunction hc C (n+1)) :
    aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (z • f) =
      z • aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      exact (ordinary_head_integral_ordinary_coefficient_row_class hc C Ξ hΞ hNames γ hγ hγ1 F.2 Z
        (ordinaryFamilyHeadPreparation hc Ξ hGenerated F.2)
        (ordinaryFamilyHeadPreparation hc Ξ hGenerated (F.2.prodZero Z)) x).trans
        (volume_family_zero_product_row_scalar hc
          (F.2.headIntegral hc Ξ (ordinaryFamilyHeadPreparation hc Ξ hGenerated F.2)) Z x).symm

def aeOrdinaryRVVolumeHeadIntegralOrdinaryLinearMap (n : ℕ) :
    AEOrdinaryRVVolumeFunction hc C (n+1) →ₗ[RVVolumeBlowupClasses hc C 0] AERVVolumeFunction hc C n 0 where
  toAddHom := aeOrdinaryRVVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  map_smul' := ae_ordinary_head_integral_ordinary_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1
end IntegrationInACVF.Section7
