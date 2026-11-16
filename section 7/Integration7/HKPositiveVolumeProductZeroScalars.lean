import Integration7.AERVVolumePositiveCoefficientAssociativity
import Integration7.ZeroCoefficientProductSymmetry
import Integration7.HKZeroCoefficientScalarRows
import Integration7.HKAERVWeightedZeroModules

/-! Weighted RV[0] coefficients are central in actual graded volume
products. Only this degree-zero centrality is used for the two scalar
compatibilities; no positive-product commutativity is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p k : ℕ}

theorem weighted_volume_smul_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C U =
      positiveVolumeBlowupClass hc C (positiveZeroProduct U Z) :=
  (zero_volume_coefficient_smul_eq_right_product hc C _ _).trans
    (positiveVolumeBlowupClass_iso hc C (productPositiveZeroIso hc C U Z))

theorem weighted_volume_coefficient_of_mul_commute
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVBlowupClasses hc C 0) (v : PositiveVolumeBlowupClasses hc C k) :
    DirectSum.of (RVBlowupClasses hc C) 0 z * DirectSum.of (RVBlowupClasses hc C) (k+1) v =
      DirectSum.of (RVBlowupClasses hc C) (k+1) v * DirectSum.of (RVBlowupClasses hc C) 0 z := by
  letI : ∀ d, AddCommMonoid (RVBlowupClasses hc C d) := rvVolumeBlowupClassesAddCommMonoid hc C
  rw [DirectSum.of_mul_of,DirectSum.of_mul_of]
  have h : GradedMonoid.mk (0+(k+1)) (rvVolumeBlowupClassesProduct hc C 0 (k+1) z v) =
      GradedMonoid.mk ((k+1)+0) (rvVolumeBlowupClassesProduct hc C (k+1) 0 v z) :=
    Sigma.ext (by change 0+(k+1)=(k+1)+0; omega) (rv_volume_blowup_classes_zero_product_swap hc C z v)
  exact DirectSum.of_eq_of_gradedMonoid_eq h

theorem rv_volume_smul_positive_product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (v : PositiveVolumeBlowupClasses hc C k) :
    rvVolumeBlowupClassesProduct hc C (p+1) (k+1) (z • u) v =
      z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v := by
  letI : ∀ d, AddCommMonoid (RVBlowupClasses hc C d) := rvVolumeBlowupClassesAddCommMonoid hc C
  let A := RVBlowupClasses hc C
  apply (show Function.Injective (DirectSum.of A ((p+1)+(k+1))) from DFinsupp.single_injective)
  calc
    DirectSum.of A ((p+1)+(k+1)) (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) (z • u) v) =
        DirectSum.of A (p+1) (z • u) * DirectSum.of A (k+1) v := (DirectSum.of_mul_of (i := p+1) (j := k+1) _ _).symm
    _ = (DirectSum.of A 0 z * DirectSum.of A (p+1) u) * DirectSum.of A (k+1) v := by rw [DirectSum.of_zero_smul]
    _ = DirectSum.of A 0 z * (DirectSum.of A (p+1) u * DirectSum.of A (k+1) v) := mul_assoc _ _ _
    _ = DirectSum.of A 0 z * DirectSum.of A ((p+1)+(k+1)) (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) := by
      rw [DirectSum.of_mul_of]
      rfl
    _ = DirectSum.of A ((p+1)+(k+1)) (z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) :=
      (DirectSum.of_zero_smul A _ _).symm

theorem rv_volume_smul_positive_product_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (z : RVBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C p)
    (v : PositiveVolumeBlowupClasses hc C k) :
    rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u (z • v) =
      z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v := by
  letI : ∀ d, AddCommMonoid (RVBlowupClasses hc C d) := rvVolumeBlowupClassesAddCommMonoid hc C
  let A := RVBlowupClasses hc C
  apply (show Function.Injective (DirectSum.of A ((p+1)+(k+1))) from DFinsupp.single_injective)
  calc
    DirectSum.of A ((p+1)+(k+1)) (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u (z • v)) =
        DirectSum.of A (p+1) u * DirectSum.of A (k+1) (z • v) := (DirectSum.of_mul_of (i := p+1) (j := k+1) _ _).symm
    _ = DirectSum.of A (p+1) u * (DirectSum.of A 0 z * DirectSum.of A (k+1) v) := by rw [DirectSum.of_zero_smul]
    _ = (DirectSum.of A (p+1) u * DirectSum.of A 0 z) * DirectSum.of A (k+1) v := (mul_assoc _ _ _).symm
    _ = (DirectSum.of A 0 z * DirectSum.of A (p+1) u) * DirectSum.of A (k+1) v := by
      rw [weighted_volume_coefficient_of_mul_commute hc C z u]
    _ = DirectSum.of A 0 z * (DirectSum.of A (p+1) u * DirectSum.of A (k+1) v) := mul_assoc _ _ _
    _ = DirectSum.of A 0 z * DirectSum.of A ((p+1)+(k+1)) (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) := by
      rw [DirectSum.of_mul_of]
      rfl
    _ = DirectSum.of A ((p+1)+(k+1)) (z • rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) :=
      (DirectSum.of_zero_smul A _ _).symm

end IntegrationInACVF.Section7.HK
