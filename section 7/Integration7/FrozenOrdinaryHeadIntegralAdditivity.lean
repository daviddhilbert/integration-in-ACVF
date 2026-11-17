module

public import Integration7.FieldBaseUnaryIntegralAdditivity
public import Integration7.OrdinaryFrozenCoproductBijections
public import Integration7.FrozenOrdinaryHeadIntegralValues
public import Integration7.DefinableVolumeParameterDescent

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary RV[0] head-fibre integration preserves sums. Its unary VF
realizations have the actual unit density, and equality descends to the
original frozen real context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem ordinary_family_frozen_head_integral_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (x : Fin n → VFType (M := M)) :
    ordinaryFamilyFrozenHeadIntegral hc C Ξ (F.coprod G) x =
      ordinaryFamilyFrozenHeadIntegral hc C Ξ F x + ordinaryFamilyFrozenHeadIntegral hc C Ξ G x := by
  let D := frozenHeadVolumeContext hc C x
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  exact (unary_field_volume_integral_bijection hc D Ξ hΞ FBase hNamesD γ hγ hγ1 _ _
    (ordinaryFrozenHeadCoprodBijection hc F G x)).trans
      (unary_field_volume_integral_add hc D Ξ hΞ FBase hNamesD γ hγ hγ1 _ _)

theorem ordinary_head_integral_sum_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (E : HeadPreparation (nativeMixedVolumeDomain hc G.fullVFObject.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc (F.coprod G).fullVFObject.densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass (k := 0) hc (vfParameterVolumeContext C x) (((F.coprod G).headIntegral hc Ξ S).rowInContext x) =
      positiveVolumeBlowupClass (k := 0) hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x) +
      positiveVolumeBlowupClass (k := 0) hc (vfParameterVolumeContext C x) ((G.headIntegral hc Ξ E).rowInContext x) := by
  apply positive_volume_class_extend_injective_definable hc (vfParameterVolumeContext C x)
    (frozenHeadVolumeContext hc C x) (frozen_head_volume_context_contains hc C x)
    (definably_closed_volume_context_names hc _)
  rw [map_add,ordinary_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 _ S x,
    ordinary_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x,
    ordinary_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 G E x]
  exact ordinary_family_frozen_head_integral_add hc C Ξ hΞ hNames γ hγ hγ1 F G x
end IntegrationInACVF.Section7
