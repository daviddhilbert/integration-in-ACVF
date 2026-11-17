module

public import Integration7.OrdinaryHeadFibreIntegralIsomorphisms
public import Integration7.PositiveVolumeClassExtensions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The ordinary degree-zero case of pointwise head-fibre integration.
Its frozen VF family has the actual unit density and is integrated by
the proved field-base unary volume integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

def ordinaryFamilyFrozenHeadIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M)) :
    PositiveVolumeBlowupClasses hc (frozenHeadVolumeContext hc C x) 0 :=
  unaryFieldVolumeIntegral hc (frozenHeadVolumeContext hc C x) Ξ
    (definablyClosedVolumeContextField hc (vfParameterVolumeContext C x))
    (F.frozenHeadFamily hc x).fullVFObject

theorem ordinary_head_integral_is_frozen_fibre_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeClassExtend hc (vfParameterVolumeContext C x) (frozenHeadVolumeContext hc C x)
      (frozen_head_volume_context_contains hc C x) 0
      (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x)) =
    ordinaryFamilyFrozenHeadIntegral hc C Ξ F x := by
  let D := frozenHeadVolumeContext hc C x
  let hD := frozen_head_volume_context_contains hc C x
  let R := ordinaryHeadFibreStandardContraction hc D F T x hD
  have he := positiveVolumeBlowupClass_iso hc D (ordinaryHeadFibreIntegralVolumeIso hc D F T x hD Ξ)
  change positiveVolumeBlowupClass hc D (((F.headIntegral hc Ξ T).rowInContext x).extend hD) = _
  exact he.trans (unary_field_volume_integral_contraction hc D Ξ hΞ
    (definablyClosedVolumeContextField hc (vfParameterVolumeContext C x))
    (frozen_head_volume_context_common_names hc C Ξ hNames x) γ hγ hγ1
    (F.frozenHeadFamily hc x).fullVFObject R).symm

end IntegrationInACVF.Section7
