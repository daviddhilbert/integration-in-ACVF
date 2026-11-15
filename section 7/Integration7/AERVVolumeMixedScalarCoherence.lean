import Integration7.PositiveVolumeProductOrdinaryScalars
import Integration7.AERVVolumeOrdinaryCoefficientModules
import Integration7.PositiveVolumeClassScalarExtensions

/-! Ordinary and positive coefficient actions agree with the actual
graded product in both mixed cases. The proof is fibrewise and uses
only the proved centrality of ordinary RV[0] coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}

theorem ae_rv_volume_positive_coefficient_smul_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k (z • u) f =
      z • aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction u using Quotient.inductionOn with
    | h U =>
      induction f using Quotient.inductionOn with
      | h F =>
        change aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k
          (rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C U) (Quotient.mk _ F) =
            rvVolumeBlowupClass hc C (n := 0) Z • aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k
              (positiveVolumeBlowupClass hc C U) (Quotient.mk _ F)
        rw [ordinary_volume_smul_representative hc C Z U]
        apply Quotient.sound
        apply ae_rv_volume_function_equivalent_of_pointwise hc C
        intro x
        simp only [selected_volume_family_left_product_row_class,volume_family_zero_product_row_scalar]
        rw [← ordinary_volume_smul_representative hc C Z U,positive_volume_class_extend_smul]
        exact rv_volume_smul_positive_product_left hc (vfParameterVolumeContext C x) _ _ _

theorem ae_rv_volume_positive_coefficient_smul_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u (z • f) =
      z • aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f :=
  Quotient.inductionOn₃ z u f (fun Z U F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_left_product_row_class,volume_family_zero_product_row_scalar]
      exact rv_volume_smul_positive_product_right hc (vfParameterVolumeContext C x) _ _ _)))

end IntegrationInACVF.Section7
