import Integration7.HKZeroFamilyFieldScalarIntegrals
import Integration7.HKFrozenZeroHeadIntegralValues
import Integration7.HKPositiveVolumeClassScalarExtensions
import Integration7.HKFrozenHeadWeightedZeroCoefficients

/-! The weighted-zero input scalar law holds on the genuine frozen unary fibres and descends to the original parameter context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def zeroFrozenScalarVolumeBijection (F : ZeroVFVolumeFamily C (n+1) a)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) (x : Fin n → VFType (M := M)) :
    VFVolumeBijection (((F.prodZero Z).frozenHeadFamily hc x).fullVFObject)
      (((F.frozenHeadFamily hc x).prodZero (Z.extend
        (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))))).fullVFObject) := by
  let D := frozenHeadVolumeContext hc C x
  let A := ((F.prodZero Z).frozenHeadFamily hc x).fullVFObject
  let B := ((F.frozenHeadFamily hc x).prodZero (Z.extend
    (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))))).fullVFObject
  have hAB : A.domain.carrier=B.domain.carrier := by
    ext p
    change (Fin.cons (p.1 0) x,p.2) ∈ (mixedRVFactorDomain F.domain Z.underlying.obj.domain).carrier ↔
      (p.1,p.2) ∈ (mixedRVFactorDomain (F.frozenHeadFamily hc x).domain
        (Z.underlying.obj.domain.extend (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))))).carrier
    rw [mem_mixed_rv_factor_domain,mem_mixed_rv_factor_domain]
    rfl
  let f : Map A.domain B.domain := Map.inclusion hAB.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact Subtype.ext (congrArg (fun q : B.domain => q.val) huv)
    · intro p
      exact ⟨⟨p.val,hAB.ge p.property⟩,rfl⟩
  apply VFVolumeBijection.of_preserving_vf_and_density hc D f hf (fun _ => rfl)
  intro p
  let q := mixedRVFactorUnpack F.domain Z.underlying.obj.domain
    (⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ : (F.prodZero Z).domain)
  let r := mixedRVFactorUnpack (F.frozenHeadFamily hc x).domain
    (Z.underlying.obj.domain.extend (fun _ h => frozen_head_volume_context_contains hc C x
      (vfParameterVolumeContext_contains C x (Or.inl h)))) (f p)
  change F.form.value (Map.prodFst _ _ q) * Z.form.value (Map.prodSnd _ _ q) =
    F.form.value ⟨(Fin.cons ((Map.prodFst _ _ r).val.1 0) x,(Map.prodFst _ _ r).val.2),_⟩ *
      Z.form.value ⟨(Map.prodSnd _ _ r).val,_⟩
  have hq := mixed_rv_factor_unpack_value F.domain Z.underlying.obj.domain
    (⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ : (F.prodZero Z).domain)
  have hr := mixed_rv_factor_unpack_value (F.frozenHeadFamily hc x).domain
    (Z.underlying.obj.domain.extend (fun _ h => frozen_head_volume_context_contains hc C x
      (vfParameterVolumeContext_contains C x (Or.inl h)))) (f p)
  congr 1
  · congr 1
    apply Subtype.ext
    have hLq : (Map.prodFst _ _ q).val =
        (Fin.cons (p.val.1 0) x,p.val.2 ∘ Fin.castAdd Z.underlying.obj.arity) := congrArg Prod.fst hq
    have hLr : (Map.prodFst _ _ r).val =
        (p.val.1,p.val.2 ∘ Fin.castAdd Z.underlying.obj.arity) := congrArg Prod.fst hr
    change (Map.prodFst _ _ q).val =
      (Fin.cons ((Map.prodFst _ _ r).val.1 0) x,(Map.prodFst _ _ r).val.2)
    rw [hLq,hLr]
  · congr 1
    apply Subtype.ext
    exact (congrArg Prod.snd hq).trans (congrArg Prod.snd hr).symm

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem zero_family_frozen_head_integral_weighted_coefficient
    (F : ZeroVFVolumeFamily C (n+1) a) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    zeroFamilyFrozenHeadIntegral hc C Ξ (F.prodZero Z) x =
      zeroVolumeCoefficientExtend hc C (frozenHeadVolumeContext hc C x)
        (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h)))
        (rvVolumeBlowupClass hc C (n := 0) Z) • zeroFamilyFrozenHeadIntegral hc C Ξ F x := by
  let D := frozenHeadVolumeContext hc C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))
  let V := Z.extend hCD
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  have h := unary_field_volume_integral_bijection hc D Ξ hΞ FBase hNamesD γ hγ hγ1 _ _
    (zeroFrozenScalarVolumeBijection hc C F Z x)
  exact h.trans (zero_family_unary_field_integral_weighted_coefficient hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    (F.frozenHeadFamily hc x) V)

theorem zero_head_integral_weighted_coefficient_row_class
    (F : ZeroVFVolumeFamily C (n+1) a) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc (F.prodZero Z).fullVFObject.densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (((F.prodZero Z).headIntegral hc Ξ S).rowInContext x) =
      zeroVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) (rvVolumeBlowupClass hc C (n := 0) Z) •
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x) := by
  apply positive_volume_class_extend_injective_definable hc (vfParameterVolumeContext C x)
    (frozenHeadVolumeContext hc C x) (frozen_head_volume_context_contains hc C x)
    (definably_closed_volume_context_names hc _)
  let CX := vfParameterVolumeContext C x
  let D := frozenHeadVolumeContext hc C x
  let hCX : (C.base : Set M) ⊆ (CX.base : Set M) := fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  let hXD := frozen_head_volume_context_contains hc C x
  let zX := zeroVolumeCoefficientExtend hc C CX hCX (rvVolumeBlowupClass hc C (n := 0) Z)
  let fX := positiveVolumeBlowupClass hc CX ((F.headIntegral hc Ξ T).rowInContext x)
  have hProduct := weighted_positive_volume_class_extend_smul hc CX D hXD zX fX
  have hF := zero_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x
  have hH := zero_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 (F.prodZero Z) S x
  have hIntegral := zero_family_frozen_head_integral_weighted_coefficient hc C Ξ hΞ hNames γ hγ hγ1 F Z x
  exact hH.trans (hIntegral.trans ((congrArg (fun v =>
    zeroVolumeCoefficientExtend hc C D (fun _ h => hXD (hCX h)) (rvVolumeBlowupClass hc C (n := 0) Z) • v)
      hF.symm).trans hProduct.symm))
end IntegrationInACVF.Section7.HK
