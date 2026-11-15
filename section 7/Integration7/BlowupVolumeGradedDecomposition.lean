import Integration7.SemiringGroupificationAdditiveMaps
import Integration7.VolumeIntegrationGroupification

/-! The actual common-blowup ring is additively the direct sum of the completed
geometric degree components. This constructs the grading decomposition
rather than treating homogeneity as an extra assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def blowupVolumeHomogeneousAdditiveMap (n : ℕ) :
    Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n) →+ RVVolumeBlowupRing hc C :=
  Algebra.GrothendieckAddGroup.lift
    ((semiringGroupificationOf (RVVolumeBlowupSemiring hc C)).toAddMonoidHom.comp
      (DirectSum.of (RVVolumeBlowupClasses hc C) n))

abbrev BlowupVolumeGradedAddGroup := DirectSum ℕ
  (fun n => Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n))

def blowupVolumePositiveGradingMap : RVVolumeBlowupSemiring hc C →+ BlowupVolumeGradedAddGroup hc C :=
  DirectSum.toAddMonoid (fun n =>
    (DirectSum.of (fun n => Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n)) n).comp
      Algebra.GrothendieckAddGroup.of)

def blowupVolumeDecomposition : RVVolumeBlowupRing hc C →+ BlowupVolumeGradedAddGroup hc C :=
  semiringGroupificationAdditiveLift (blowupVolumePositiveGradingMap hc C)

theorem blowup_volume_decomposition_of_homogeneous (n : ℕ) (a : RVVolumeBlowupClasses hc C n) :
    blowupVolumeDecomposition hc C (semiringGroupificationOf _ (DirectSum.of _ n a))=
      DirectSum.of (fun n => Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n)) n
        (Algebra.GrothendieckAddGroup.of a) := by
  rw [blowupVolumeDecomposition,semiring_groupification_additive_lift_of]
  exact DirectSum.toAddMonoid_of _ n a

def blowupVolumeComposition : BlowupVolumeGradedAddGroup hc C →+ RVVolumeBlowupRing hc C :=
  DirectSum.toAddMonoid (blowupVolumeHomogeneousAdditiveMap hc C)

theorem blowup_volume_composition_of (n : ℕ)
    (a : Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n)) :
    blowupVolumeComposition hc C (DirectSum.of _ n a)=blowupVolumeHomogeneousAdditiveMap hc C n a :=
  by simpa only [blowupVolumeComposition] using
    (DirectSum.toAddMonoid_of (blowupVolumeHomogeneousAdditiveMap hc C) n a)

theorem blowup_volume_homogeneous_additive_map_of (n : ℕ) (a : RVVolumeBlowupClasses hc C n) :
    blowupVolumeHomogeneousAdditiveMap hc C n (Algebra.GrothendieckAddGroup.of a)=
      semiringGroupificationOf _ (DirectSum.of _ n a) :=
  Algebra.GrothendieckAddGroup.lift_apply_of _ a

theorem blowup_volume_grading_left_inverse :
    Function.LeftInverse (blowupVolumeComposition hc C) (blowupVolumeDecomposition hc C) := by
  have h : (blowupVolumeComposition hc C).comp (blowupVolumeDecomposition hc C)=AddMonoidHom.id _ := by
    apply semiring_groupification_additive_hom_ext
    intro a
    change blowupVolumeComposition hc C (blowupVolumeDecomposition hc C (semiringGroupificationOf _ a))=_
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero,AddMonoidHom.id_apply]
    | of n a =>
      rw [blowup_volume_decomposition_of_homogeneous,blowup_volume_composition_of,blowup_volume_homogeneous_additive_map_of]
      rfl
    | add a b ha hb =>
      simp only [map_add,AddMonoidHom.id_apply] at *
      rw [ha,hb]
  exact DFunLike.congr_fun h

theorem blowup_volume_grading_right_inverse :
    Function.RightInverse (blowupVolumeComposition hc C) (blowupVolumeDecomposition hc C) := by
  have h : (blowupVolumeDecomposition hc C).comp (blowupVolumeComposition hc C)=AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro n a
    obtain ⟨x,y,rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of a
    change blowupVolumeDecomposition hc C (blowupVolumeComposition hc C (DirectSum.of _ n
      (Algebra.GrothendieckAddGroup.of x-Algebra.GrothendieckAddGroup.of y)))=_
    simp only [map_sub,blowup_volume_composition_of,blowup_volume_homogeneous_additive_map_of,
      blowup_volume_decomposition_of_homogeneous,AddMonoidHom.id_apply]
  exact DFunLike.congr_fun h

def blowupVolumeGradedAddEquiv : RVVolumeBlowupRing hc C ≃+ BlowupVolumeGradedAddGroup hc C :=
  { blowupVolumeDecomposition hc C with
    invFun := blowupVolumeComposition hc C
    left_inv := blowup_volume_grading_left_inverse hc C
    right_inv := blowup_volume_grading_right_inverse hc C }
end IntegrationInACVF.Section7
