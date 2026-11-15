import Integration7.AEOrdinaryPositiveCoefficientBilinearity
import Integration7.AEOrdinaryVolumeModules
import Integration7.AERVVolumeOrdinaryCoefficientModules
import Integration7.PositiveVolumeClassScalarExtensions

/-! Multiplication from ordinary-valued AE functions to positive-valued
AE functions is bilinear over the ordinary coefficient semiring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}

theorem ae_ordinary_positive_coefficient_smul_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p (z • u) f =
      z • aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction u using Quotient.inductionOn with
    | h U =>
      induction f using Quotient.inductionOn with
      | h F =>
        change aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p
          (rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C U) (Quotient.mk _ F) = _
        rw [ordinary_volume_smul_representative hc C Z U]
        apply Quotient.sound
        apply ae_rv_volume_function_equivalent_of_pointwise hc C
        intro x
        rw [selected_ordinary_family_positive_product_row_class,volume_family_zero_product_row_scalar,
          selected_ordinary_family_positive_product_row_class]
        rw [← ordinary_volume_smul_representative hc C Z U,positive_volume_class_extend_smul]
        exact smul_comm _ _ _

theorem ae_ordinary_positive_coefficient_smul_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u (z • f) =
      z • aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u f :=
  Quotient.inductionOn₃ z u f (fun Z U F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      rw [selected_ordinary_family_positive_product_row_class,volume_family_zero_product_row_scalar,
        selected_ordinary_family_positive_product_row_class,ordinary_volume_family_scalar_row_class]
      exact mul_smul _ _ _)))

def aeOrdinaryRVVolumeFunctionPositiveCoefficientBilinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p : ℕ) :
    PositiveVolumeBlowupClasses hc C p →ₗ[RVVolumeBlowupClasses hc C 0]
      (AEOrdinaryRVVolumeFunction hc C n →ₗ[RVVolumeBlowupClasses hc C 0] AERVVolumeFunction hc C n p) where
  toFun u := {
    toAddHom := aeOrdinaryRVVolumeFunctionPositiveCoefficientBiadditive hc C n p u
    map_smul' z f := ae_ordinary_positive_coefficient_smul_right hc C z u f }
  map_add' u v := LinearMap.ext (fun f => ae_ordinary_positive_coefficient_add hc C u v f)
  map_smul' z u := LinearMap.ext (fun f => ae_ordinary_positive_coefficient_smul_left hc C z u f)

end IntegrationInACVF.Section7
