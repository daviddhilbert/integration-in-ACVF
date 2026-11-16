module

public import Integration7.AERVVolumeRestrictionAdditivity
public import Integration7.SupportedOrdinaryVolumeCoefficients
public import Integration7.SupportedPositiveVolumeCoefficients

@[expose] public section

/-! Restriction commutes with every actual homogeneous coefficient
action, including ordinary RV[0]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}

theorem ae_volume_restriction_ordinary_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (z : RVVolumeBlowupClasses hc C 0) (f : AERVVolumeFunction hc C n k) :
    aeVolumeFunctionRestrictToSupported hc C X (z • f) = z • aeVolumeFunctionRestrictToSupported hc C X f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      change positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
          (((F.2.prodZero Z).onBase X).rowInContext x) =
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (((F.2.onBase X).prodZero Z).rowInContext x)
      rw [volume_family_zero_product_row_scalar]
      by_cases hx : x ∈ X.carrier
      · rw [selected_volume_on_base_row_class_inside hc _ X x hx,volume_family_zero_product_row_scalar,
          selected_volume_on_base_row_class_inside hc F.2 X x hx]
      · rw [selected_volume_on_base_row_class_outside hc _ X x hx,
          selected_volume_on_base_row_class_outside hc F.2 X x hx,smul_zero]

theorem ae_volume_restriction_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (u : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C n k) :
    aeVolumeFunctionRestrictToSupported hc C X (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f) =
      supportedPositiveVolumeCoefficientProduct hc C X u (aeVolumeFunctionRestrictToSupported hc C X f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      change positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
          (((selectedVolumeFamilyLeftProduct U F.2).onBase X).rowInContext x) =
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
          ((selectedVolumeFamilyLeftProduct U (F.2.onBase X)).rowInContext x)
      rw [selected_volume_family_left_product_row_class]
      by_cases hx : x ∈ X.carrier
      · rw [selected_volume_on_base_row_class_inside hc _ X x hx,selected_volume_family_left_product_row_class,
          selected_volume_on_base_row_class_inside hc F.2 X x hx]
      · rw [selected_volume_on_base_row_class_outside hc _ X x hx,
          selected_volume_on_base_row_class_outside hc F.2 X x hx]
        exact (DirectSum.GNonUnitalNonAssocSemiring.mul_zero
          (A := RVVolumeBlowupClasses hc (vfParameterVolumeContext C x)) (i := p+1) (j := k+1) _).symm

def aeVolumeRestrictionOrdinaryLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    AERVVolumeFunction hc C n k →ₗ[RVVolumeBlowupClasses hc C 0] SupportedAERVVolumeFunction hc C X k where
  toAddHom := aeVolumeRestrictionAddHom (k := k) hc C X
  map_smul' := fun z f => ae_volume_restriction_ordinary_coefficient hc C X z f
end IntegrationInACVF.Section7
