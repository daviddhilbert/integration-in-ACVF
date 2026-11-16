module

public import Integration7.AEVolumeComponentHeadIntegrals
public import Integration7.EmptyHeadIntegralFamilies

@[expose] public section

/-! First-head integration sends zero to zero in every homogeneous degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_ordinary_head_integral_zero (n : ℕ) :
    aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (0 : AEOrdinaryRVVolumeFunction hc C (n+1)) = 0 := by
  let F := ordinaryZeroVolumeFamily C ((n+1)+1)
  let T := ordinaryFamilyHeadPreparation hc Ξ hGenerated F
  change (Quotient.mk _ ⟨_,F.headIntegral hc Ξ T⟩ : AERVVolumeFunction hc C n 0) = 0
  apply ae_volume_function_of_empty_family hc
  apply head_preparation_empty_contracted_domain _ T
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨q,hq⟩
  exact q.property

theorem ae_positive_head_integral_zero (n k : ℕ) :
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (0 : AERVVolumeFunction hc C (n+1) k) = 0 := by
  let F := selectedZeroVolumeFamily C ((n+1)+1) k
  let T := selectedFamilyHeadPreparation hc Ξ hGenerated F
  change (Quotient.mk _ ⟨_,F.headIntegral hc Ξ T⟩ : AERVVolumeFunction hc C n (k+1)) = 0
  apply ae_volume_function_of_empty_family hc
  apply head_preparation_empty_contracted_domain _ T
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨q,hq⟩
  exact q.property

theorem ae_volume_component_head_integral_zero (n j : ℕ) :
    aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j 0 = 0 := by
  cases j with
  | zero => exact ae_ordinary_head_integral_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  | succ k => exact ae_positive_head_integral_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k

end IntegrationInACVF.Section7
