import Integration7.AERVVolumePositiveCoefficientAssociativity
import Integration7.ZeroCoefficientProductSymmetry
import Integration7.OrdinaryVolumeCoefficientScalarRows

/-! Ordinary RV[0] coefficients are central in actual graded volume
products. Only this degree-zero centrality is used for the two scalar
compatibilities; no positive-product commutativity is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p k : ℕ}

theorem ordinary_volume_smul_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C U =
      positiveVolumeBlowupClass hc C (U.prod_zero Z) :=
  (ordinary_volume_coefficient_smul_eq_right_product hc C _ _).trans
    (positiveVolumeBlowupClass_iso hc C (volumeProductPositiveZeroIso hc C U Z))

theorem ordinary_volume_coefficient_of_mul_commute
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (v : PositiveVolumeBlowupClasses hc C k) :
    DirectSum.of (RVVolumeBlowupClasses hc C) 0 z * DirectSum.of (RVVolumeBlowupClasses hc C) (k+1) v =
      DirectSum.of (RVVolumeBlowupClasses hc C) (k+1) v * DirectSum.of (RVVolumeBlowupClasses hc C) 0 z := by
  rw [DirectSum.of_mul_of,DirectSum.of_mul_of]
  have h : GradedMonoid.mk (0+(k+1)) (rvVolumeBlowupClassesProduct hc C 0 (k+1) z v) =
      GradedMonoid.mk ((k+1)+0) (rvVolumeBlowupClassesProduct hc C (k+1) 0 v z) :=
    Sigma.ext (by change 0+(k+1)=(k+1)+0; omega) (rv_volume_blowup_classes_zero_product_swap hc C z v)
  exact DirectSum.of_eq_of_gradedMonoid_eq h

theorem rv_volume_smul_positive_product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (v : PositiveVolumeBlowupClasses hc C k) :
    rvVolumeBlowupClassesProduct hc C (p+1) (k+1) (z • u) v =
      z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v := by
  let A := RVVolumeBlowupClasses hc C
  apply (show Function.Injective (DirectSum.of A ((p+1)+(k+1))) from DFinsupp.single_injective)
  calc
    DirectSum.of A _ (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) (z • u) v) =
        DirectSum.of A _ (z • u) * DirectSum.of A _ v := (DirectSum.of_mul_of _ _).symm
    _ = (DirectSum.of A 0 z * DirectSum.of A _ u) * DirectSum.of A _ v := by rw [DirectSum.of_zero_smul]
    _ = DirectSum.of A 0 z * (DirectSum.of A _ u * DirectSum.of A _ v) := mul_assoc _ _ _
    _ = DirectSum.of A 0 z * DirectSum.of A _ (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) := by
      rw [DirectSum.of_mul_of]
      rfl
    _ = DirectSum.of A _ (z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) :=
      (DirectSum.of_zero_smul A _ _).symm

theorem rv_volume_smul_positive_product_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVVolumeBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (v : PositiveVolumeBlowupClasses hc C k) :
    rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u (z • v) =
      z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v := by
  let A := RVVolumeBlowupClasses hc C
  apply (show Function.Injective (DirectSum.of A ((p+1)+(k+1))) from DFinsupp.single_injective)
  calc
    DirectSum.of A _ (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u (z • v)) =
        DirectSum.of A _ u * DirectSum.of A _ (z • v) := (DirectSum.of_mul_of _ _).symm
    _ = DirectSum.of A _ u * (DirectSum.of A 0 z * DirectSum.of A _ v) := by rw [DirectSum.of_zero_smul]
    _ = (DirectSum.of A _ u * DirectSum.of A 0 z) * DirectSum.of A _ v := (mul_assoc _ _ _).symm
    _ = (DirectSum.of A 0 z * DirectSum.of A _ u) * DirectSum.of A _ v := by
      rw [ordinary_volume_coefficient_of_mul_commute hc C z u]
    _ = DirectSum.of A 0 z * (DirectSum.of A _ u * DirectSum.of A _ v) := mul_assoc _ _ _
    _ = DirectSum.of A 0 z * DirectSum.of A _ (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) := by
      rw [DirectSum.of_mul_of]
      rfl
    _ = DirectSum.of A _ (z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) :=
      (DirectSum.of_zero_smul A _ _).symm

end IntegrationInACVF.Section7
