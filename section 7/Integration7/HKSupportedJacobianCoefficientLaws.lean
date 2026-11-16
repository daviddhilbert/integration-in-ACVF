module

public import Integration7.HKJacobianCoefficientRowClasses
public import Integration7.HKSupportedGradedActions
public import Integration7.SupportedVolumeJacobianPositiveCoefficients

@[expose] public section

/-! The actual supported Jacobian transforms commute with the genuine
weighted coefficient operations on both zero and positive components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
variable (φ : Map X Y) (hφ : Function.Bijective φ)

theorem supported_positive_jacobian_weighted_coefficient
    (z : RVBlowupClasses hc C 0) (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionJacobian hc C φ hφ (supportedPositiveWeightedCoefficientProduct hc C X z f) =
      supportedPositiveWeightedCoefficientProduct hc C Y z (supportedVolumeFunctionJacobian hc C φ hφ f) := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      exact (selected_jacobian_weighted_coefficient_row_class hc C φ hφ Z F.2.val F.2.property y).trans
        (selected_family_weighted_zero_row_scalar hc
          (F.2.val.jacobianPushforward φ hφ F.2.property) Z y).symm

theorem supported_zero_jacobian_weighted_coefficient
    (z : RVBlowupClasses hc C 0) (f : SupportedAEZeroVolumeFunction hc C X) :
    supportedZeroVolumeFunctionJacobian hc C φ hφ (supportedZeroWeightedCoefficientProduct hc C X z f) =
      supportedZeroWeightedCoefficientProduct hc C Y z (supportedZeroVolumeFunctionJacobian hc C φ hφ f) := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_zero_volume_equivalent_of_pointwise hc C
      intro y
      exact (zero_jacobian_weighted_coefficient_row_class hc C φ hφ Z F.2.val F.2.property y).trans
        (zero_volume_family_scalar_row_class hc
          (F.2.val.jacobianPushforward φ hφ F.2.property) Z y).symm

theorem supported_zero_jacobian_positive_coefficient
    (u : PositiveVolumeBlowupClasses hc C p) (f : SupportedAEZeroVolumeFunction hc C X) :
    supportedVolumeFunctionJacobian hc C φ hφ (supportedZeroPositiveCoefficientProduct hc C X u f) =
      supportedZeroPositiveCoefficientProduct hc C Y u (supportedZeroVolumeFunctionJacobian hc C φ hφ f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      exact (zero_jacobian_positive_coefficient_row_class hc C φ hφ U F.2.val F.2.property y).trans
        (selected_zero_family_positive_product_row_class hc U
          (F.2.val.jacobianPushforward φ hφ F.2.property) y).symm

theorem supported_component_jacobian_weighted_coefficient (j : ℕ)
    (z : RVBlowupClasses hc C 0) (f : SupportedVolumeFunctionComponent hc C X j) :
    supportedVolumeComponentJacobianAddHom hc C φ hφ j (supportedVolumeComponentWeightedCoefficient hc C X j z f) =
      supportedVolumeComponentWeightedCoefficient hc C Y j z (supportedVolumeComponentJacobianAddHom hc C φ hφ j f) := by
  cases j with
  | zero => exact supported_zero_jacobian_weighted_coefficient hc C φ hφ z f
  | succ k => exact supported_positive_jacobian_weighted_coefficient hc C φ hφ z f

theorem supported_component_jacobian_degree_heq {i j : ℕ} (h : i=j)
    (f : SupportedVolumeFunctionComponent hc C X i) :
    HEq (supportedVolumeComponentJacobianAddHom hc C φ hφ j (gradedDegreeAddEquiv h f))
      (supportedVolumeComponentJacobianAddHom hc C φ hφ i f) := by
  cases h
  rfl

theorem supported_component_jacobian_coefficient (i j : ℕ)
    (u : RVBlowupClasses hc C i) (f : SupportedVolumeFunctionComponent hc C X j) :
    supportedVolumeComponentJacobianAddHom hc C φ hφ (i+j) (supportedVolumeComponentCoefficient hc C X i j u f) =
      supportedVolumeComponentCoefficient hc C Y i j u (supportedVolumeComponentJacobianAddHom hc C φ hφ j f) := by
  cases i with
  | zero =>
    have hL := supported_component_jacobian_degree_heq hc C φ hφ (Nat.zero_add j).symm
      (supportedVolumeComponentWeightedCoefficient hc C X j u f)
    have hR := graded_degree_add_equiv_heq (F := SupportedVolumeFunctionComponent hc C Y)
      (Nat.zero_add j).symm
      (supportedVolumeComponentWeightedCoefficient hc C Y j u (supportedVolumeComponentJacobianAddHom hc C φ hφ j f))
    exact eq_of_heq (hL.trans ((heq_of_eq (supported_component_jacobian_weighted_coefficient hc C φ hφ j u f)).trans hR.symm))
  | succ p =>
    cases j with
    | zero => exact supported_zero_jacobian_positive_coefficient hc C φ hφ u f
    | succ k => exact supported_volume_jacobian_positive_coefficient hc C φ hφ u f

def supportedGradedVolumeJacobianLinearMap :
    SupportedGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C] SupportedGradedVolumeFunction hc C Y :=
  gradedSemiringActionLinearMap (supportedVolumeGradedAction hc C X) (supportedVolumeGradedAction hc C Y)
    (supportedVolumeComponentJacobianAddHom hc C φ hφ) (supported_component_jacobian_coefficient hc C φ hφ)

theorem supported_graded_volume_jacobian_linear_value (f : SupportedGradedVolumeFunction hc C X) :
    supportedGradedVolumeJacobianLinearMap hc C φ hφ f = supportedGradedVolumeJacobianAddHom hc C φ hφ f := rfl

end IntegrationInACVF.Section7.HK
