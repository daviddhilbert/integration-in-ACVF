import Integration7.HKZeroFamilyPositiveFieldIntegralProducts
import Integration7.FrozenHeadIntegralAdditivity
import Integration7.HKFrozenZeroHeadIntegralValues
import Integration7.HKPositiveVolumeClassScalarExtensions
import Integration7.HKPositiveVolumeClassProductExtensions
import Integration7.DefinableVolumeParameterDescent

/-! Positive coefficient products commute with genuine weighted-zero frozen fibre integration. The head-row identity descends to the original parameter context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem zero_frozen_head_family_row_class
    (F : ZeroVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M)) (y : Fin 1 → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y) (n := 0)
      ((F.frozenHeadFamily hc x).rowInContext y) =
    zeroVolumeCoefficientExtend hc (vfParameterVolumeContext C (Fin.cons (y 0) x))
      (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      (head_fibre_row_context_contains C _ x (frozen_head_volume_context_contains hc C x) y)
      (rvVolumeBlowupClass hc (vfParameterVolumeContext C (Fin.cons (y 0) x)) (n := 0)
        (F.rowInContext (Fin.cons (y 0) x))) := rfl

theorem zero_frozen_head_positive_coefficient_row_class
    (F : ZeroVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) (y : Fin 1 → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      (((selectedZeroFamilyPositiveProduct U F).frozenHeadFamily hc x).rowInContext y) =
    positiveVolumeBlowupClass hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      ((selectedZeroFamilyPositiveProduct
        (U.extend (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))))
        (F.frozenHeadFamily hc x)).rowInContext y) := by
  rw [selected_frozen_head_family_row_class,selected_zero_family_positive_product_row_class,
    weighted_positive_volume_class_extend_smul,selected_zero_family_positive_product_row_class,
    zero_frozen_head_family_row_class]
  rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem zero_family_frozen_head_appended_integral_positive_coefficient
    (F : ZeroVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ (selectedZeroFamilyPositiveProduct U F) x =
      rvVolumeBlowupClassesProduct hc (frozenHeadVolumeContext hc C x) (p+1) 1
        (positiveVolumeBlowupClass hc (frozenHeadVolumeContext hc C x)
          (U.extend (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h)))))
        (zeroFamilyFrozenHeadIntegral hc C Ξ F x) := by
  let D := frozenHeadVolumeContext hc C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))
  let V := U.extend hCD
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  have h := selected_family_field_appended_integral_independent hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    ((selectedZeroFamilyPositiveProduct U F).frozenHeadFamily hc x) (selectedZeroFamilyPositiveProduct V (F.frozenHeadFamily hc x))
    (fun y => (positiveVolumeBlowupClass_eq_iff hc _).mp (zero_frozen_head_positive_coefficient_row_class hc C F U x y))
  exact h.trans (zero_family_field_appended_integral_positive_coefficient hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    (F.frozenHeadFamily hc x) V)

theorem zero_head_integral_positive_coefficient_row_class
    (F : ZeroVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc (selectedZeroFamilyPositiveProduct U F).densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (((selectedZeroFamilyPositiveProduct U F).headIntegral hc Ξ S).rowInContext x) =
      rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C x) (p+1) 1
        (positiveVolumeClassExtend hc C (vfParameterVolumeContext C x)
          (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) p (positiveVolumeBlowupClass hc C U))
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x)) := by
  apply positive_volume_class_extend_injective_definable hc (vfParameterVolumeContext C x)
    (frozenHeadVolumeContext hc C x) (frozen_head_volume_context_contains hc C x)
    (definably_closed_volume_context_names hc _)
  let CX := vfParameterVolumeContext C x
  let D := frozenHeadVolumeContext hc C x
  let hCX : (C.base : Set M) ⊆ (CX.base : Set M) := fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  let hXD := frozen_head_volume_context_contains hc C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) := fun _ h => hXD (hCX h)
  let uX := positiveVolumeClassExtend hc C CX hCX p (positiveVolumeBlowupClass hc C U)
  let fX := positiveVolumeBlowupClass hc CX ((F.headIntegral hc Ξ T).rowInContext x)
  have hProduct := positive_volume_class_extend_product hc CX D hXD (p := p) (q := 0) uX fX
  have hU : positiveVolumeClassExtend hc CX D hXD p uX=positiveVolumeBlowupClass hc D (U.extend hCD) := rfl
  have hF := zero_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x
  have hH := selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1
    (selectedZeroFamilyPositiveProduct U F) S x
  have hIntegral := zero_family_frozen_head_appended_integral_positive_coefficient hc C Ξ hΞ hNames γ hγ hγ1 F U x
  exact hH.trans (hIntegral.trans ((congrArg₂ (rvVolumeBlowupClassesProduct hc D (p+1) 1)
    hU.symm hF.symm).trans hProduct.symm))
end IntegrationInACVF.Section7.HK
