module

public import Integration7.AERVVolumeZeroCoefficientProducts
public import Integration7.OrdinaryVolumeCoefficientExtensions
public import Integration7.ZeroCoefficientProductSymmetry

@[expose] public section

/-! The finite-factor family action is the usual grade-zero scalar
action on every actual RV fibre, after the genuine base-extension hom.
Moving a degree-zero factor changes no volume coordinate order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem ordinary_volume_coefficient_smul_eq_right_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (v : PositiveVolumeBlowupClasses hc C k) :
    z • v = rvVolumeBlowupClassesProduct hc C (k+1) 0 v z := by
  have h : HEq (z • v) (rvVolumeBlowupClassesProduct hc C 0 (k+1) z v) := eqRec_heq _ _
  exact eq_of_heq (h.trans (rv_volume_blowup_classes_zero_product_swap hc C z v))

theorem volume_family_zero_product_row_scalar
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.prodZero Z).rowInContext x) =
      ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) (rvVolumeBlowupClass hc C (n := 0) Z) •
          positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x) := by
  let D := vfParameterVolumeContext C x
  let U := F.rowInContext x
  let z := ordinaryVolumeCoefficientInContext Z x
  have hRow := positiveVolumeBlowupClass_iso hc D (volumeFamilyZeroProductRowIso hc F Z x)
  have hProduct := positiveVolumeBlowupClass_iso hc D (volumeProductPositiveZeroIso hc D U z)
  have hScalar := ordinary_volume_coefficient_smul_eq_right_product hc D
    (rvVolumeBlowupClass hc D (n := 0) z) (positiveVolumeBlowupClass hc D U)
  exact hRow.trans (hProduct.symm.trans hScalar.symm)

end IntegrationInACVF.Section7
