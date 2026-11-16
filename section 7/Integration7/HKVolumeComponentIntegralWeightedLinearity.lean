module

public import Integration7.HKAppendedVolumeIntegralWeightedZeroLinearMaps
public import Integration7.HKAEZeroIntegralLinearMap
public import Integration7.HKGradedAEVolumeIntegralAddHoms

@[expose] public section

/-! Every actual homogeneous integral is linear over weighted measured
zero; arithmetic degree changes retain this same scalar action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def aeVolumeFunctionComponentIntegralLinearMap (n j : ℕ) :
    AEVolumeFunctionComponent hc C n j →ₗ[RVBlowupClasses hc C 0] PositiveVolumeBlowupClasses hc C (n+j) where
  toAddHom := aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
  map_smul' z f := by
    cases j with
    | zero => exact ae_zero_volume_integral_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 z f
    | succ k =>
      have h : n+(k+1)=appendVolumeDegree (n+1) k := by rw [append_volume_degree_eq]; omega
      let E := positiveVolumeClassDegreeReindexWeightedZeroLinearEquiv hc C h
      let I := aeRVVolumeFunctionAppendedIntegralWeightedZeroLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
      exact (E.toLinearMap.comp I).map_smul z f

theorem ae_volume_component_integral_heq {n a b : ℕ} (h : a=b)
    {f : AEVolumeFunctionComponent hc C n a} {g : AEVolumeFunctionComponent hc C n b} (hfg : HEq f g) :
    HEq (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n a f)
      (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n b g) := by
  cases h
  cases hfg
  rfl


theorem rv_volume_product_heq_of_inputs {i i' j j' : ℕ} (hi : i=i') (hj : j=j')
    {u : RVBlowupClasses hc C i} {v : RVBlowupClasses hc C i'}
    {a : RVBlowupClasses hc C j} {b : RVBlowupClasses hc C j'} (huv : HEq u v) (hab : HEq a b) :
    HEq (rvVolumeBlowupClassesProduct hc C i j u a)
      (rvVolumeBlowupClassesProduct hc C i' j' v b) := by
  cases hi
  cases hj
  cases huv
  cases hab
  rfl

end IntegrationInACVF.Section7.HK
