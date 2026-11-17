module

public import Integration7.HKSelectedJacobianWeightedScalarRows
public import Integration7.HKZeroJacobianWeightedScalarRows
public import Integration7.HKZeroJacobianPositiveCoefficientRows
public import Integration7.HKSupportedCoefficientProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Weighted Jacobian scalar identities hold on every target row,
including the literal empty rows outside the target support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
variable (φ : Map X Y) (hφ : Function.Bijective φ)

theorem selected_jacobian_weighted_coefficient_row_class
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) (F : SelectedVFVolumeFamily C n a k)
    (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) (y : Fin n → Transfer.VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
      (((selectedFamilyWeightedZeroProduct F Z).jacobianPushforward φ hφ
        (mixed_finite_factor_preserves_support F.domain Z.underlying.obj.domain hF)).rowInContext y) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) (zeroVolumeCoefficientInContext Z y) •
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C y) ((F.jacobianPushforward φ hφ hF).rowInContext y) := by
  by_cases hy : y ∈ Y.carrier
  · exact selected_jacobian_row_weighted_scalar_comparison hc C Z F (selectedFamilyWeightedZeroProduct F Z)
      φ hφ hF _ ⟨y,hy⟩ (selected_family_weighted_zero_row_scalar hc F Z _)
  · have hEmpty {d j : ℕ} (H : SelectedVFVolumeFamily C n d j)
        (hH : ∀ q : H.domain, q.val.1 ∈ X.carrier) :
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C y) ((H.jacobianPushforward φ hφ hH).rowInContext y) = 0 :=
      positiveVolumeBlowupClass_iso hc _ (RVVolumeIso.of_empty hc _ _ _
        (selected_jacobian_row_empty_outside C H φ hφ hH y hy) rfl)
    rw [hEmpty,hEmpty,smul_zero]

theorem zero_jacobian_weighted_coefficient_row_class
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) (F : ZeroVFVolumeFamily C n a)
    (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) (y : Fin n → Transfer.VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0)
      (((F.prodZero Z).jacobianPushforward φ hφ
        (mixed_finite_factor_preserves_support F.domain Z.underlying.obj.domain hF)).rowInContext y) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) (zeroVolumeCoefficientInContext Z y) *
        rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) ((F.jacobianPushforward φ hφ hF).rowInContext y) := by
  by_cases hy : y ∈ Y.carrier
  · exact zero_jacobian_row_weighted_scalar_comparison hc C Z F (F.prodZero Z)
      φ hφ hF _ ⟨y,hy⟩ (zero_volume_family_scalar_row_class hc F Z _)
  · have hEmpty {d : ℕ} (H : ZeroVFVolumeFamily C n d)
        (hH : ∀ q : H.domain, q.val.1 ∈ X.carrier) :
        rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) ((H.jacobianPushforward φ hφ hH).rowInContext y) = 0 :=
      zero_rv_volume_class_of_empty hc _ _ (zero_jacobian_row_empty_outside C H φ hφ hH y hy)
    rw [hEmpty,hEmpty,mul_zero]

theorem zero_jacobian_positive_coefficient_row_class
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : ZeroVFVolumeFamily C n a)
    (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) (y : Fin n → Transfer.VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
      (((selectedZeroFamilyPositiveProduct U F).jacobianPushforward φ hφ
        (selected_zero_positive_product_supported U F hF)).rowInContext y) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) ((F.jacobianPushforward φ hφ hF).rowInContext y) •
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C y) (positiveVolumeCoefficientInContext U y) := by
  by_cases hy : y ∈ Y.carrier
  · exact zero_jacobian_row_positive_coefficient_comparison hc C U F (selectedZeroFamilyPositiveProduct U F)
      φ hφ hF _ ⟨y,hy⟩ (selected_zero_family_positive_product_row_class hc U F _)
  · have hH : positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
        (((selectedZeroFamilyPositiveProduct U F).jacobianPushforward φ hφ
          (selected_zero_positive_product_supported U F hF)).rowInContext y) = 0 :=
      positiveVolumeBlowupClass_iso hc _ (RVVolumeIso.of_empty hc _ _ _
        (selected_jacobian_row_empty_outside C _ φ hφ _ y hy) rfl)
    have hZ : rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0)
        ((F.jacobianPushforward φ hφ hF).rowInContext y) = 0 :=
      zero_rv_volume_class_of_empty hc _ _ (zero_jacobian_row_empty_outside C F φ hφ hF y hy)
    rw [hH,hZ,zero_smul]

end IntegrationInACVF.Section7.HK
