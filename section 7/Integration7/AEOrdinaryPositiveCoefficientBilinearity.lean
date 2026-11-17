module

public import Integration7.AEOrdinaryPositiveCoefficientProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Positive multiplication of ordinary-valued AE functions is additive
in each argument, as verified by the actual row scalar formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}

theorem ae_ordinary_positive_coefficient_add_function
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u : PositiveVolumeBlowupClasses hc C p) (f g : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u (f+g) =
      aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u f +
        aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u g :=
  Quotient.inductionOn₃ u f g (fun U F G => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_ordinary_family_positive_product_row_class,ordinary_volume_family_coprod_row_class,
        selected_volume_family_sum_row_class]
      exact add_smul _ _ _)))

theorem ae_ordinary_positive_coefficient_zero_function
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u : PositiveVolumeBlowupClasses hc C p) :
    aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u 0 = 0 :=
  Quotient.inductionOn u (fun U => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      rw [selected_ordinary_family_positive_product_row_class,ordinary_zero_volume_family_row_class,
        selected_zero_volume_family_row_class,zero_smul])))

theorem ae_ordinary_positive_coefficient_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u v : PositiveVolumeBlowupClasses hc C p) (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p (u+v) f =
      aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u f +
        aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p v f :=
  Quotient.inductionOn₃ u v f (fun U V F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_ordinary_family_positive_product_row_class,selected_volume_family_sum_row_class]
      change _ • positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ p
        (positiveVolumeBlowupClass hc C U + positiveVolumeBlowupClass hc C V) = _
      rw [map_add,smul_add])))

theorem ae_ordinary_positive_zero_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p 0 f = 0 :=
  Quotient.inductionOn f (fun F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_ordinary_family_positive_product_row_class,selected_zero_volume_family_row_class]
      change _ • positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ p 0 = 0
      rw [map_zero,smul_zero])))

def aeOrdinaryRVVolumeFunctionPositiveCoefficientBiadditive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p : ℕ) :
    PositiveVolumeBlowupClasses hc C p →+ (AEOrdinaryRVVolumeFunction hc C n →+ AERVVolumeFunction hc C n p) where
  toFun u := {
    toFun := aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n p u
    map_zero' := ae_ordinary_positive_coefficient_zero_function hc C u
    map_add' := ae_ordinary_positive_coefficient_add_function hc C u }
  map_zero' := AddMonoidHom.ext (ae_ordinary_positive_zero_coefficient hc C)
  map_add' u v := AddMonoidHom.ext (ae_ordinary_positive_coefficient_add hc C u v)

end IntegrationInACVF.Section7
