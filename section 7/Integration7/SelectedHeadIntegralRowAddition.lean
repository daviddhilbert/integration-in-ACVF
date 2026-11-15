import Integration7.FrozenHeadIntegralAdditivity
import Integration7.DefinableVolumeParameterDescent

/-! The head-integral row of a sum is the sum of its actual two rows.
Equality descends from the definable closure of the frozen parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_head_integral_sum_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (E : HeadPreparation (nativeMixedVolumeDomain hc G.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc (selectedVolumeFamilySum F G).densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (((selectedVolumeFamilySum F G).headIntegral hc Ξ S).rowInContext x) =
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x) +
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((G.headIntegral hc Ξ E).rowInContext x) := by
  apply positive_volume_class_extend_injective_definable hc (vfParameterVolumeContext C x)
    (frozenHeadVolumeContext hc C x) (frozen_head_volume_context_contains hc C x)
    (definably_closed_volume_context_names hc _)
  rw [map_add,selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 _ S x,
    selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x,
    selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 G E x]
  exact selected_family_frozen_head_appended_integral_add hc C Ξ hΞ hNames γ hγ hγ1 F G x
end IntegrationInACVF.Section7
