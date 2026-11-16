module

public import Integration7.SelectedVolumeDensityRescaling
public import Integration7.AERVVolumeOrdinaryCoefficientModules
public import Integration7.AERVVolumePositiveCoefficientBilinearity
public import Integration7.DefinableRescalingOrdinaryCoefficients
public import Integration7.DefinableRescalingProducts

@[expose] public section

/-! Actual positive AE density rescaling is linear over ordinary
coefficients and also commutes with every positive coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)

theorem ae_rv_volume_density_rescale_add (f g : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionRescale hc C c hcS hc0 (f+g)=
      aeRVVolumeFunctionRescale hc C c hcS hc0 f+aeRVVolumeFunctionRescale hc C c hcS hc0 g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      rw [selected_volume_rescale_row_class,selected_volume_family_sum_row_class,
        selected_volume_family_sum_row_class,selected_volume_rescale_row_class,selected_volume_rescale_row_class]
      exact map_add _ _ _

theorem ae_rv_volume_density_rescale_zero :
    aeRVVolumeFunctionRescale hc C (n := n) (k := k) c hcS hc0 0=0 := by
  apply Quotient.sound
  apply ae_rv_volume_function_equivalent_of_pointwise hc C
  intro x
  rw [selected_volume_rescale_row_class,selected_zero_volume_family_row_class]
  exact map_zero _

theorem ae_rv_volume_density_rescale_smul (z : RVVolumeBlowupClasses hc C 0)
    (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionRescale hc C c hcS hc0 (z • f)=z • aeRVVolumeFunctionRescale hc C c hcS hc0 f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      rw [selected_volume_rescale_row_class,volume_family_zero_product_row_scalar,
        volume_family_zero_product_row_scalar,selected_volume_rescale_row_class]
      exact positive_volume_class_rescale_definable_smul hc (vfParameterVolumeContext C x) c _ hc0 _ _

def aeRVVolumeFunctionRescaleOrdinaryLinearMap (n k : ℕ) :
    AERVVolumeFunction hc C n k →ₗ[RVVolumeBlowupClasses hc C 0] AERVVolumeFunction hc C n k where
  toFun := aeRVVolumeFunctionRescale hc C c hcS hc0
  map_add' := ae_rv_volume_density_rescale_add hc C c hcS hc0
  map_smul' := ae_rv_volume_density_rescale_smul hc C c hcS hc0

theorem ae_rv_volume_rescale_positive_coefficient (u : PositiveVolumeBlowupClasses hc C p)
    (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionRescale hc C c hcS hc0 (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f)=
      aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u (aeRVVolumeFunctionRescale hc C c hcS hc0 f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      rw [selected_volume_rescale_row_class,selected_volume_family_left_product_row_class,
        selected_volume_family_left_product_row_class,selected_volume_rescale_row_class]
      exact positive_volume_class_rescale_definable_product hc (vfParameterVolumeContext C x) c _ hc0 _ _
end IntegrationInACVF.Section7
