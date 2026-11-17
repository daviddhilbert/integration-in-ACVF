module

public import Integration7.HKFrozenZeroHeadIntegralAdditivity
public import Integration7.HKAEZeroHeadIntegrals
public import Integration7.EmptyHeadIntegralFamilies
public import Integration7.AERVVolumeFunctionAdditiveStructure
public import Integration7.HKAEZeroFunctionAddition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual weighted degree-zero partial integral is additive on
almost-everywhere classes and creates its genuine first volume coordinate. -/
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

theorem ae_zero_head_integral_zero (n : ℕ) :
    aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (0 : AEZeroVolumeFunction hc C (n+1)) = 0 := by
  let F := zeroFamily C ((n+1)+1)
  let T := zeroFamilyHeadPreparation hc Ξ hGenerated F
  change (Quotient.mk _ ⟨_,F.headIntegral hc Ξ T⟩ : AERVVolumeFunction hc C n 0) = 0
  apply ae_volume_function_of_empty_family hc
  apply head_preparation_empty_contracted_domain _ T
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨q,hq⟩
  exact q.property

theorem ae_zero_volume_head_integral_add
    (f g : AEZeroVolumeFunction hc C (n+1)) :
    aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (f+g) =
      aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f +
      aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      exact (zero_head_integral_sum_row_class hc C Ξ hΞ hNames γ hγ hγ1 F.2 G.2
        (zeroFamilyHeadPreparation hc Ξ hGenerated F.2)
        (zeroFamilyHeadPreparation hc Ξ hGenerated G.2)
        (zeroFamilyHeadPreparation hc Ξ hGenerated (F.2.coprod G.2)) x).trans
        (selected_volume_family_sum_row_class hc
          (F.2.headIntegral hc Ξ (zeroFamilyHeadPreparation hc Ξ hGenerated F.2))
          (G.2.headIntegral hc Ξ (zeroFamilyHeadPreparation hc Ξ hGenerated G.2)) x).symm

def aeZeroVolumeHeadIntegralAddHom (n : ℕ) :
    AEZeroVolumeFunction hc C (n+1) →+ AERVVolumeFunction hc C n 0 where
  toFun := aeZeroVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  map_zero' := ae_zero_head_integral_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  map_add' := ae_zero_volume_head_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1
end IntegrationInACVF.Section7.HK
