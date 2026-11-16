module

public import Integration7.UnitPointVolumeSwaps
public import Integration7.ZeroCoefficientProductSymmetry
public import Integration7.AllDegreeVolumeBlowupSemiring

@[expose] public section

/-! The concrete degree-one point class is central in the actual full
graded common-blowup semiring, including its ordinary degree-zero part. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumePointClass
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) : RVVolumeBlowupSemiring hc C :=
  DirectSum.of (RVVolumeBlowupClasses hc C) 1
    (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))

theorem volume_point_product_swap_positive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    HEq
      (rvVolumeBlowupClassesProduct hc C (k+1) 1 (rvVolumeBlowupClass hc C (n := k+1) U)
        (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))))
      (rvVolumeBlowupClassesProduct hc C 1 (k+1)
        (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))
        (rvVolumeBlowupClass hc C (n := k+1) U)) := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  exact positive_volume_blowup_class_heq_of_cast_iso hc C (positiveProduct_degree_swap k 0)
    (U.prod P) (P.prod U)
    ((volumeUnitPointSwapIso C U).trans hc C (volumeCastReindexIso hc C (P.prod U) _))

theorem volume_point_class_commutes_component
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (j : ℕ) (a : RVVolumeBlowupClasses hc C j) :
    Commute (DirectSum.of (RVVolumeBlowupClasses hc C) j a) (volumePointClass hc C) := by
  change DirectSum.of (RVVolumeBlowupClasses hc C) j a *
      DirectSum.of (RVVolumeBlowupClasses hc C) 1 _ =
    DirectSum.of (RVVolumeBlowupClasses hc C) 1 _ * DirectSum.of (RVVolumeBlowupClasses hc C) j a
  rw [DirectSum.of_mul_of,DirectSum.of_mul_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (Nat.add_comm j 1)
  cases j with
  | zero => exact rv_volume_blowup_classes_zero_product_swap hc C a _
  | succ k =>
    induction a using Quotient.inductionOn with
    | h U => exact volume_point_product_swap_positive hc C U

theorem volume_point_class_commutes
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a : RVVolumeBlowupSemiring hc C) : Commute a (volumePointClass hc C) := by
  induction a using DirectSum.induction_on with
  | zero => exact Commute.zero_left _
  | of j a => exact volume_point_class_commutes_component hc C j a
  | add a b ha hb => exact ha.add_left hb

end IntegrationInACVF.Section7
