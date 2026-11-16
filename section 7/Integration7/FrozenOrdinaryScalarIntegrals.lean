module

public import Integration7.OrdinaryFamilyFieldScalarIntegrals
public import Integration7.FrozenOrdinaryCoefficientProducts
public import Integration7.FrozenHeadOrdinaryCoefficients

@[expose] public section

/-! The ordinary-input finite coefficient law holds on the genuine
frozen unary fibres and descends to the original parameter context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def ordinaryFrozenScalarVolumeBijection (F : OrdinaryVFVolumeFamily C (n+1) a)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) (x : Fin n → VFType (M := M)) :
    VFVolumeBijection (((F.prodZero Z).frozenHeadFamily hc x).fullVFObject)
      (((F.frozenHeadFamily hc x).prodZero (Section6.FiniteRV.extendObject
        (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))) Z)).fullVFObject) := by
  let D := frozenHeadVolumeContext hc C x
  let A := ((F.prodZero Z).frozenHeadFamily hc x).fullVFObject
  let B := ((F.frozenHeadFamily hc x).prodZero (Section6.FiniteRV.extendObject
    (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))) Z)).fullVFObject
  have hAB : A.domain.carrier=B.domain.carrier := by
    ext p
    change (Fin.cons (p.1 0) x,p.2) ∈ (mixedRVFactorDomain F.domain Z.obj.domain).carrier ↔
      (p.1,p.2) ∈ (mixedRVFactorDomain (F.frozenHeadFamily hc x).domain
        (Z.obj.domain.extend (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))))).carrier
    rw [mem_mixed_rv_factor_domain,mem_mixed_rv_factor_domain]
    rfl
  let f : Map A.domain B.domain := Map.inclusion hAB.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact Subtype.ext (congrArg (fun q : B.domain => q.val) huv)
    · intro p
      exact ⟨⟨p.val,hAB.ge p.property⟩,rfl⟩
  exact VFVolumeBijection.of_preserving_vf_and_density hc D f hf (fun _ => rfl) (fun _ => rfl)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem ordinary_family_frozen_head_integral_ordinary_coefficient
    (F : OrdinaryVFVolumeFamily C (n+1) a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    ordinaryFamilyFrozenHeadIntegral hc C Ξ (F.prodZero Z) x =
      ordinaryVolumeCoefficientExtend hc C (frozenHeadVolumeContext hc C x)
        (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h)))
        (rvVolumeBlowupClass hc C (n := 0) Z) • ordinaryFamilyFrozenHeadIntegral hc C Ξ F x := by
  let D := frozenHeadVolumeContext hc C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))
  let V := Section6.FiniteRV.extendObject hCD Z
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  have h := unary_field_volume_integral_bijection hc D Ξ hΞ FBase hNamesD γ hγ hγ1 _ _
    (ordinaryFrozenScalarVolumeBijection hc C F Z x)
  exact h.trans (ordinary_family_unary_field_integral_ordinary_coefficient hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    (F.frozenHeadFamily hc x) V)

theorem ordinary_head_integral_ordinary_coefficient_row_class
    (F : OrdinaryVFVolumeFamily C (n+1) a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc (F.prodZero Z).fullVFObject.densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (((F.prodZero Z).headIntegral hc Ξ S).rowInContext x) =
      ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) (rvVolumeBlowupClass hc C (n := 0) Z) •
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x) := by
  apply positive_volume_class_extend_injective_definable hc (vfParameterVolumeContext C x)
    (frozenHeadVolumeContext hc C x) (frozen_head_volume_context_contains hc C x)
    (definably_closed_volume_context_names hc _)
  let CX := vfParameterVolumeContext C x
  let D := frozenHeadVolumeContext hc C x
  let hCX : (C.base : Set M) ⊆ (CX.base : Set M) := fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  let hXD := frozen_head_volume_context_contains hc C x
  let zX := ordinaryVolumeCoefficientExtend hc C CX hCX (rvVolumeBlowupClass hc C (n := 0) Z)
  let fX := positiveVolumeBlowupClass hc CX ((F.headIntegral hc Ξ T).rowInContext x)
  have hProduct := positive_volume_class_extend_smul hc CX D hXD zX fX
  have hF := ordinary_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x
  have hH := ordinary_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 (F.prodZero Z) S x
  have hIntegral := ordinary_family_frozen_head_integral_ordinary_coefficient hc C Ξ hΞ hNames γ hγ hγ1 F Z x
  exact hH.trans (hIntegral.trans ((congrArg (fun v =>
    ordinaryVolumeCoefficientExtend hc C D (fun _ h => hXD (hCX h)) (rvVolumeBlowupClass hc C (n := 0) Z) • v)
      hF.symm).trans hProduct.symm))
end IntegrationInACVF.Section7
