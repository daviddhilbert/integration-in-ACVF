module

public import Integration7.HKZeroCoefficientSemiring
public import Integration7.HKZeroCoefficientSymmetry

@[expose] public section

/-! The actual weighted grade-zero scalar action is right Cartesian
multiplication after moving the zero factor, without a VF permutation. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance zeroCoefficientPositiveModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Module (RVBlowupClasses hc C 0) (PositiveVolumeBlowupClasses hc C k) := by
  letI : ∀ n, AddCommMonoid (RVBlowupClasses hc C n) := rvVolumeBlowupClassesAddCommMonoid hc C
  exact inferInstanceAs (Module (RVBlowupClasses hc C 0) (RVBlowupClasses hc C (k+1)))

theorem zero_volume_coefficient_smul_eq_right_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (z : RVBlowupClasses hc C 0) (v : PositiveVolumeBlowupClasses hc C k) :
    z • v = rvVolumeBlowupClassesProduct hc C (k+1) 0 v z := by
  have h : HEq (z • v) (rvVolumeBlowupClassesProduct hc C 0 (k+1) z v) := eqRec_heq _ _
  exact eq_of_heq (h.trans (rv_volume_blowup_classes_zero_product_swap hc C z v))

end IntegrationInACVF.Section7.HK
