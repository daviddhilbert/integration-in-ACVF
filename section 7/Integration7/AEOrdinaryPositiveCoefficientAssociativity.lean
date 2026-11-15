import Integration7.AEOrdinaryPositiveCoefficientProducts
import Integration7.AERVVolumePositiveCoefficientBilinearity
import Integration7.PositiveVolumeClassProductExtensions
import Integration7.PositiveVolumeProductOrdinaryScalars

/-! Positive coefficient multiplication associates when its innermost
function is ordinary-valued, with the literal graded product degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}

theorem ae_ordinary_positive_coefficient_assoc
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u : PositiveVolumeBlowupClasses hc C p) (v : PositiveVolumeBlowupClasses hc C k)
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u
      (aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n k v f) =
      aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n ((p+1)+k)
        (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) f :=
  Quotient.inductionOn₃ u v f (fun U V F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_left_product_row_class,selected_ordinary_family_positive_product_row_class]
      change rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C x) (p+1) (k+1)
        (positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ p (positiveVolumeBlowupClass hc C U))
        (rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.2.rowInContext x) •
          positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ k (positiveVolumeBlowupClass hc C V)) =
        rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.2.rowInContext x) •
          positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ ((p+1)+k)
            (rvVolumeBlowupClassesProduct hc C (p+1) (k+1)
              (positiveVolumeBlowupClass hc C U) (positiveVolumeBlowupClass hc C V))
      rw [positive_volume_class_extend_product,rv_volume_smul_positive_product_right])))

end IntegrationInACVF.Section7
