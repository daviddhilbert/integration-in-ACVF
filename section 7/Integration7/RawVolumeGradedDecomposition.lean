module

public import Integration7.RawVolumeDegreeComponents

@[expose] public section

/-! The actual raw ring is additively the direct sum of the completed
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

abbrev RawVolumeGradedAddGroup := DirectSum ℕ
  (fun n => Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n))

def rawVolumePositiveGradingMap : RVVolumeIsoSemiring hc C →+ RawVolumeGradedAddGroup hc C :=
  DirectSum.toAddMonoid (fun n =>
    (DirectSum.of (fun n => Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) n).comp
      Algebra.GrothendieckAddGroup.of)

def rawVolumeDecomposition : RawRVVolumeRing hc C →+ RawVolumeGradedAddGroup hc C :=
  semiringGroupificationAdditiveLift (rawVolumePositiveGradingMap hc C)

theorem raw_volume_decomposition_of_homogeneous (n : ℕ) (a : RVVolumeIsoClasses hc C n) :
    rawVolumeDecomposition hc C (semiringGroupificationOf _ (DirectSum.of _ n a))=
      DirectSum.of (fun n => Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) n
        (Algebra.GrothendieckAddGroup.of a) := by
  rw [rawVolumeDecomposition,semiring_groupification_additive_lift_of]
  exact DirectSum.toAddMonoid_of _ n a

def rawVolumeComposition : RawVolumeGradedAddGroup hc C →+ RawRVVolumeRing hc C :=
  DirectSum.toAddMonoid (rawVolumeHomogeneousAdditiveMap hc C)

theorem raw_volume_composition_of (n : ℕ)
    (a : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) :
    rawVolumeComposition hc C (DirectSum.of _ n a)=rawVolumeHomogeneousAdditiveMap hc C n a :=
  by simpa only [rawVolumeComposition] using
    (DirectSum.toAddMonoid_of (rawVolumeHomogeneousAdditiveMap hc C) n a)

theorem raw_volume_homogeneous_additive_map_of (n : ℕ) (a : RVVolumeIsoClasses hc C n) :
    rawVolumeHomogeneousAdditiveMap hc C n (Algebra.GrothendieckAddGroup.of a)=
      semiringGroupificationOf _ (DirectSum.of _ n a) :=
  Algebra.GrothendieckAddGroup.lift_apply_of _ a

theorem raw_volume_grading_left_inverse :
    Function.LeftInverse (rawVolumeComposition hc C) (rawVolumeDecomposition hc C) := by
  have h : (rawVolumeComposition hc C).comp (rawVolumeDecomposition hc C)=AddMonoidHom.id _ := by
    apply semiring_groupification_additive_hom_ext
    intro a
    change rawVolumeComposition hc C (rawVolumeDecomposition hc C (semiringGroupificationOf _ a))=_
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero,AddMonoidHom.id_apply]
    | of n a =>
      rw [raw_volume_decomposition_of_homogeneous,raw_volume_composition_of,raw_volume_homogeneous_additive_map_of]
      rfl
    | add a b ha hb =>
      simp only [map_add,AddMonoidHom.id_apply] at *
      rw [ha,hb]
  exact DFunLike.congr_fun h

theorem raw_volume_grading_right_inverse :
    Function.RightInverse (rawVolumeComposition hc C) (rawVolumeDecomposition hc C) := by
  have h : (rawVolumeDecomposition hc C).comp (rawVolumeComposition hc C)=AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro n a
    obtain ⟨x,y,rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of a
    change rawVolumeDecomposition hc C (rawVolumeComposition hc C (DirectSum.of _ n
      (Algebra.GrothendieckAddGroup.of x-Algebra.GrothendieckAddGroup.of y)))=_
    simp only [map_sub,raw_volume_composition_of,raw_volume_homogeneous_additive_map_of,
      raw_volume_decomposition_of_homogeneous,AddMonoidHom.id_apply]
  exact DFunLike.congr_fun h

def rawVolumeGradedAddEquiv : RawRVVolumeRing hc C ≃+ RawVolumeGradedAddGroup hc C :=
  { rawVolumeDecomposition hc C with
    invFun := rawVolumeComposition hc C
    left_inv := raw_volume_grading_left_inverse hc C
    right_inv := raw_volume_grading_right_inverse hc C }
end IntegrationInACVF.Section7
