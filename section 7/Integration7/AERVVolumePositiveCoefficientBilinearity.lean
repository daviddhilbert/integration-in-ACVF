module

public import Integration7.AERVVolumePositiveCoefficientProducts
public import Integration7.PositiveVolumeClassExtensions
public import Integration7.AERVVolumeFunctionAdditiveStructure

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual positive-coefficient action is additive separately in
the coefficient and function. These are equalities of AE functions, proved
from their genuine fibre product classes and graded distributivity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

theorem selected_volume_family_left_product_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((selectedVolumeFamilyLeftProduct U F).rowInContext x) =
      rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C x) (p+1) (k+1)
        (positiveVolumeClassExtend hc C (vfParameterVolumeContext C x)
          (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) p (positiveVolumeBlowupClass hc C U))
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x)) :=
  positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x) (selectedVolumeFamilyLeftProductRowIso hc U F x)

theorem ae_rv_volume_positive_coefficient_add_function
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u : PositiveVolumeBlowupClasses hc C p) (f g : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u (f+g) =
      aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f +
        aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u g :=
  Quotient.inductionOn₃ u f g (fun U F G => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_left_product_row_class,selected_volume_family_sum_row_class]
      exact DirectSum.GNonUnitalNonAssocSemiring.mul_add
        (A := RVVolumeBlowupClasses hc (vfParameterVolumeContext C x)) _ _ _)))

theorem ae_rv_volume_positive_coefficient_zero_function
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u : PositiveVolumeBlowupClasses hc C p) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u 0 = 0 :=
  Quotient.inductionOn u (fun U => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_left_product_row_class,selected_zero_volume_family_row_class]
      exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero
        (A := RVVolumeBlowupClasses hc (vfParameterVolumeContext C x)) _)))

theorem ae_rv_volume_positive_coefficient_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u v : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k (u+v) f =
      aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f +
        aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k v f :=
  Quotient.inductionOn₃ u v f (fun U V F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_left_product_row_class,selected_volume_family_sum_row_class]
      change rvVolumeBlowupClassesProduct _ _ (p+1) (k+1)
        ((positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ p)
          (positiveVolumeBlowupClass hc C U + positiveVolumeBlowupClass hc C V)) _ = _
      rw [map_add]
      exact DirectSum.GNonUnitalNonAssocSemiring.add_mul
        (A := RVVolumeBlowupClasses hc (vfParameterVolumeContext C x)) _ _ _)))

theorem ae_rv_volume_positive_zero_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (f : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k 0 f = 0 :=
  Quotient.inductionOn f (fun F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_left_product_row_class,selected_zero_volume_family_row_class]
      change rvVolumeBlowupClassesProduct _ _ (p+1) (k+1)
        ((positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ p) 0) _ = 0
      rw [map_zero]
      exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul
        (A := RVVolumeBlowupClasses hc (vfParameterVolumeContext C x)) _)))

def aeRVVolumeFunctionPositiveCoefficientBiadditive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p k : ℕ) :
    PositiveVolumeBlowupClasses hc C p →+ (AERVVolumeFunction hc C n k →+ AERVVolumeFunction hc C n ((p+1)+k)) where
  toFun u := {
    toFun := aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u
    map_zero' := ae_rv_volume_positive_coefficient_zero_function hc C u
    map_add' := ae_rv_volume_positive_coefficient_add_function hc C u }
  map_zero' := AddMonoidHom.ext (ae_rv_volume_positive_zero_coefficient hc C)
  map_add' u v := AddMonoidHom.ext (ae_rv_volume_positive_coefficient_add hc C u v)

end IntegrationInACVF.Section7
