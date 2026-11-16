module

public import Integration7.OrdinaryCoefficientFieldIntegrals
public import Integration7.FrozenHeadIntegralAdditivity
public import Integration7.PositiveVolumeClassScalarExtensions
public import Integration7.DefinableVolumeParameterDescent

@[expose] public section

/-! Finite ordinary coefficients commute with positive-family frozen
integrals and actual original-context head rows before normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem selected_frozen_head_ordinary_coefficient_row_class
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (Z : SpecialTransformations.Section4.RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) (y : Fin 1 → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      (((F.prodZero Z).frozenHeadFamily hc x).rowInContext y) =
    positiveVolumeBlowupClass hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      (((F.frozenHeadFamily hc x).prodZero
        (Section6.FiniteRV.extendObject
          (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))) Z)).rowInContext y) := by
  rw [selected_frozen_head_family_row_class,volume_family_zero_product_row_scalar,positive_volume_class_extend_smul,
    volume_family_zero_product_row_scalar,selected_frozen_head_family_row_class]
  rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem selected_family_frozen_head_appended_integral_ordinary_coefficient
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (Z : SpecialTransformations.Section4.RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ (F.prodZero Z) x =
      ordinaryVolumeCoefficientExtend hc C (frozenHeadVolumeContext hc C x)
        (fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h)))
        (rvVolumeBlowupClass hc C (n := 0) Z) • selectedFamilyFrozenHeadAppendedIntegral hc C Ξ F x := by
  let D := frozenHeadVolumeContext hc C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => frozen_head_volume_context_contains hc C x (vfParameterVolumeContext_contains C x (Or.inl h))
  let V := Section6.FiniteRV.extendObject hCD Z
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  have h := selected_family_field_appended_integral_independent hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    ((F.prodZero Z).frozenHeadFamily hc x) ((F.frozenHeadFamily hc x).prodZero V)
    (fun y => (positiveVolumeBlowupClass_eq_iff hc _).mp (selected_frozen_head_ordinary_coefficient_row_class hc C F Z x y))
  exact h.trans (selected_family_field_appended_integral_ordinary_coefficient hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    (F.frozenHeadFamily hc x) V)

theorem selected_head_integral_ordinary_coefficient_row_class
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (Z : SpecialTransformations.Section4.RVFiniteObject (M := M) (C.base : Set M) 0)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc (F.prodZero Z).densityGraph.domain))
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
  have hF := selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x
  have hH := selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 (F.prodZero Z) S x
  have hIntegral := selected_family_frozen_head_appended_integral_ordinary_coefficient hc C Ξ hΞ hNames γ hγ hγ1 F Z x
  exact hH.trans (hIntegral.trans ((congrArg (fun v =>
    ordinaryVolumeCoefficientExtend hc C D (fun _ h => hXD (hCX h)) (rvVolumeBlowupClass hc C (n := 0) Z) • v)
      hF.symm).trans hProduct.symm))
end IntegrationInACVF.Section7
