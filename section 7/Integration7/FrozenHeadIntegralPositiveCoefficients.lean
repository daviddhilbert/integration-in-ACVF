import Integration7.PositiveConstantFieldIntegralProducts
import Integration7.SelectedHeadIntegralRowAddition
import Integration7.PositiveVolumeClassProductExtensions
import Integration7.AERVVolumePositiveCoefficientBilinearity

/-! Genuine frozen unary fibre integrals commute with positive constant
coefficients. Definable parameter descent gives the actual head-row
identity over the original frozen parameter context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem selected_frozen_head_positive_coefficient_row_class
    (F : SelectedVFVolumeFamily C (n+1) a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) (y : Fin 1 → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      (((selectedVolumeFamilyLeftProduct U F).frozenHeadFamily hc x).rowInContext y) =
    positiveVolumeBlowupClass hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      ((selectedVolumeFamilyLeftProduct
        (U.extend (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))))
        (F.frozenHeadFamily hc x)).rowInContext y) := by
  rw [selected_frozen_head_family_row_class,selected_volume_family_left_product_row_class,
    positive_volume_class_extend_product,selected_volume_family_left_product_row_class,
    selected_frozen_head_family_row_class]
  rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem selected_family_frozen_head_appended_integral_positive_coefficient
    (F : SelectedVFVolumeFamily C (n+1) a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ (selectedVolumeFamilyLeftProduct U F) x =
      rvVolumeBlowupClassesProduct hc (frozenHeadVolumeContext hc C x) (p+1) ((k+1)+1)
        (positiveVolumeBlowupClass hc (frozenHeadVolumeContext hc C x)
          (U.extend (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h)))))
        (selectedFamilyFrozenHeadAppendedIntegral hc C Ξ F x) := by
  let D := frozenHeadVolumeContext hc C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))
  let V := U.extend hCD
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  have h := selected_family_field_appended_integral_independent hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    ((selectedVolumeFamilyLeftProduct U F).frozenHeadFamily hc x) (selectedVolumeFamilyLeftProduct V (F.frozenHeadFamily hc x))
    (fun y => (positiveVolumeBlowupClass_eq_iff hc _).mp (selected_frozen_head_positive_coefficient_row_class hc C F U x y))
  change selectedFamilyFieldAppendedIntegral hc D Ξ FBase ((selectedVolumeFamilyLeftProduct U F).frozenHeadFamily hc x) = _
  exact h.trans (selected_family_field_appended_integral_positive_coefficient hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    (F.frozenHeadFamily hc x) V)

theorem selected_head_integral_positive_coefficient_row_class
    (F : SelectedVFVolumeFamily C (n+1) a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc (selectedVolumeFamilyLeftProduct U F).densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (((selectedVolumeFamilyLeftProduct U F).headIntegral hc Ξ S).rowInContext x) =
      rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C x) (p+1) ((k+1)+1)
        (positiveVolumeClassExtend hc C (vfParameterVolumeContext C x)
          (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) p (positiveVolumeBlowupClass hc C U))
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x)) := by
  apply positive_volume_class_extend_injective_definable hc (vfParameterVolumeContext C x)
    (frozenHeadVolumeContext hc C x) (frozen_head_volume_context_contains hc C x)
    (definably_closed_volume_context_names hc _)
  let CX := vfParameterVolumeContext C x
  let D := frozenHeadVolumeContext hc C x
  let hCX : (C.base : Set M) ⊆ (CX.base : Set M) :=
    fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  let hXD := frozen_head_volume_context_contains hc C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) := fun _ h => hXD (hCX h)
  let uX := positiveVolumeClassExtend hc C CX hCX p (positiveVolumeBlowupClass hc C U)
  let fX := positiveVolumeBlowupClass hc CX ((F.headIntegral hc Ξ T).rowInContext x)
  have hProduct := positive_volume_class_extend_product hc CX D hXD (p := p) (q := k+1) uX fX
  have hU : positiveVolumeClassExtend hc CX D hXD p uX=positiveVolumeBlowupClass hc D (U.extend hCD) := rfl
  have hF := selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x
  have hH := selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1
    (selectedVolumeFamilyLeftProduct U F) S x
  have hIntegral := selected_family_frozen_head_appended_integral_positive_coefficient hc C Ξ hΞ hNames γ hγ hγ1 F U x
  exact hH.trans (hIntegral.trans ((congrArg₂ (rvVolumeBlowupClassesProduct hc D (p+1) ((k+1)+1))
    hU.symm hF.symm).trans hProduct.symm))
end IntegrationInACVF.Section7
