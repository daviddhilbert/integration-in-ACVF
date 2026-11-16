module

public import Integration7.RawVolumeGradedDecomposition
public import Integration7.BlowupVolumeGradedDecomposition

@[expose] public section

/-! The actual groupified blowup projection respects the complete
additive grading. Kernel membership is exactly componentwise kernel
membership; homogeneity is proved without a principal-ideal assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def volumeDegreeGroupProjection (n : ℕ) :
    Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) →+
      Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n) :=
  Algebra.GrothendieckAddGroup.lift
    (Algebra.GrothendieckAddGroup.of.comp (rvVolumeBlowupProjection hc C n))

theorem volume_degree_group_projection_of (n : ℕ) (a : RVVolumeIsoClasses hc C n) :
    volumeDegreeGroupProjection hc C n (Algebra.GrothendieckAddGroup.of a)=
      Algebra.GrothendieckAddGroup.of (rvVolumeBlowupProjection hc C n a) :=
  Algebra.GrothendieckAddGroup.lift_apply_of _ a

def gradedVolumeGroupProjection : RawVolumeGradedAddGroup hc C →+ BlowupVolumeGradedAddGroup hc C :=
  DirectSum.toAddMonoid (fun n =>
    (DirectSum.of (fun n => Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n)) n).comp
      (volumeDegreeGroupProjection hc C n))

theorem graded_volume_group_projection_of (n : ℕ)
    (a : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) :
    gradedVolumeGroupProjection hc C (DirectSum.of _ n a)=
      DirectSum.of _ n (volumeDegreeGroupProjection hc C n a) := by
  simpa only [gradedVolumeGroupProjection,AddMonoidHom.comp_apply,
    RawVolumeGradedAddGroup,BlowupVolumeGradedAddGroup] using
    (DirectSum.toAddMonoid_of (fun n =>
      (DirectSum.of (fun n => Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n)) n).comp
        (volumeDegreeGroupProjection hc C n)) n a)

theorem graded_volume_group_projection_component (n : ℕ) (a : RawVolumeGradedAddGroup hc C) :
    (gradedVolumeGroupProjection hc C a) n=volumeDegreeGroupProjection hc C n (a n) := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero]; exact (map_zero _).symm
  | of j a =>
    rw [graded_volume_group_projection_of]
    by_cases h : n=j
    · subst j
      rw [DirectSum.of_eq_same,DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ h,DirectSum.of_eq_of_ne _ _ _ h,map_zero]
  | add a b ha hb =>
    rw [map_add]
    change (gradedVolumeGroupProjection hc C a) n+(gradedVolumeGroupProjection hc C b) n=
      volumeDegreeGroupProjection hc C n (a n+b n)
    rw [map_add,ha,hb]

theorem raw_volume_projection_grading :
    (blowupVolumeDecomposition hc C).comp (rawVolumeBlowupRingProjection hc C).toAddMonoidHom=
      (gradedVolumeGroupProjection hc C).comp (rawVolumeDecomposition hc C) := by
  apply semiring_groupification_additive_hom_ext
  intro a
  change blowupVolumeDecomposition hc C
    (semiringGroupificationMap (rvVolumeGradedBlowupProjection hc C) (semiringGroupificationOf _ a))=
      gradedVolumeGroupProjection hc C (rawVolumeDecomposition hc C (semiringGroupificationOf _ a))
  rw [semiringGroupificationMap_of]
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n a =>
    rw [rvVolumeGradedBlowupProjection_of,blowup_volume_decomposition_of_homogeneous,
      raw_volume_decomposition_of_homogeneous,graded_volume_group_projection_of,volume_degree_group_projection_of]
  | add a b ha hb =>
    simp only [map_add] at *
    rw [ha,hb]

theorem raw_volume_kernel_iff_degree_components (x : RawRVVolumeRing hc C) :
    x ∈ rawVolumeKernelIdeal hc C ↔
      ∀ n, volumeDegreeGroupProjection hc C n ((rawVolumeDecomposition hc C x) n)=0 := by
  have h := DFunLike.congr_fun (raw_volume_projection_grading hc C) x
  change blowupVolumeDecomposition hc C (rawVolumeBlowupRingProjection hc C x)=
    gradedVolumeGroupProjection hc C (rawVolumeDecomposition hc C x) at h
  constructor
  · intro hx n
    have hz : gradedVolumeGroupProjection hc C (rawVolumeDecomposition hc C x)=0 := by
      rw [←h,RingHom.mem_ker.mp hx,map_zero]
    have hn := congrArg (fun z : BlowupVolumeGradedAddGroup hc C => z n) hz
    rw [graded_volume_group_projection_component] at hn
    exact hn
  · intro hx
    apply RingHom.mem_ker.mpr
    apply (blowupVolumeGradedAddEquiv hc C).injective
    change blowupVolumeDecomposition hc C (rawVolumeBlowupRingProjection hc C x)=
      blowupVolumeDecomposition hc C 0
    rw [h,map_zero]
    ext n
    rw [graded_volume_group_projection_component]
    exact hx n
end IntegrationInACVF.Section7
