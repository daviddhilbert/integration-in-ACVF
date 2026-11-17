module

public import Integration7.BlowupVolumeGradedDecomposition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The completed geometric degree pieces retain their actual product:
degree n times degree m is in degree n+m, and the unit has degree zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem blowup_volume_homogeneous_mul_of (n m : ℕ)
    (a : RVVolumeBlowupClasses hc C n) (b : RVVolumeBlowupClasses hc C m) :
    blowupVolumeHomogeneousAdditiveMap hc C n (Algebra.GrothendieckAddGroup.of a) *
      blowupVolumeHomogeneousAdditiveMap hc C m (Algebra.GrothendieckAddGroup.of b) =
    blowupVolumeHomogeneousAdditiveMap hc C (n+m)
      (Algebra.GrothendieckAddGroup.of (rvVolumeBlowupClassesProduct hc C n m a b)) := by
  rw [blowup_volume_homogeneous_additive_map_of,blowup_volume_homogeneous_additive_map_of,
    blowup_volume_homogeneous_additive_map_of,← map_mul,DirectSum.of_mul_of]
  rfl

theorem blowup_volume_homogeneous_product_closed (n m : ℕ)
    (x : Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n))
    (y : Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C m)) :
    ∃ z : Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C (n+m)),
      blowupVolumeHomogeneousAdditiveMap hc C n x * blowupVolumeHomogeneousAdditiveMap hc C m y =
        blowupVolumeHomogeneousAdditiveMap hc C (n+m) z := by
  obtain ⟨a,b,rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨c,d,rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of y
  exact ⟨(Algebra.GrothendieckAddGroup.of (rvVolumeBlowupClassesProduct hc C n m a c)-
      Algebra.GrothendieckAddGroup.of (rvVolumeBlowupClassesProduct hc C n m a d))-
      (Algebra.GrothendieckAddGroup.of (rvVolumeBlowupClassesProduct hc C n m b c)-
      Algebra.GrothendieckAddGroup.of (rvVolumeBlowupClassesProduct hc C n m b d)),by
    simp only [map_sub,mul_sub,sub_mul,blowup_volume_homogeneous_mul_of]
    abel⟩

theorem blowup_volume_homogeneous_unit :
    blowupVolumeHomogeneousAdditiveMap hc C 0
      (Algebra.GrothendieckAddGroup.of (1 : RVVolumeBlowupClasses hc C 0))=1 := by
  rw [blowup_volume_homogeneous_additive_map_of]
  exact map_one (semiringGroupificationOf (RVVolumeBlowupSemiring hc C))
end IntegrationInACVF.Section7
