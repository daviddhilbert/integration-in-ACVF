import Integration7.SemiringGroupificationAdditiveMaps
import Integration7.RawPositiveKernelPresentation

/-! Actual homogeneous additive components of the raw ring, and the
zero degree of its geometric kernel. Ordinary degree-zero coefficients
already contribute no kernel; deleting them does not remove positive
source relations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def rawVolumeDegreeComponent (n : ℕ) : RawRVVolumeRing hc C →+
    Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) :=
  semiringGroupificationAdditiveLift
    (Algebra.GrothendieckAddGroup.of.comp (DFinsupp.evalAddMonoidHom n))

theorem raw_volume_degree_component_of (n : ℕ) (a : RVVolumeIsoSemiring hc C) :
    rawVolumeDegreeComponent hc C n (semiringGroupificationOf _ a)=
      Algebra.GrothendieckAddGroup.of (a n) :=
  semiring_groupification_additive_lift_of _ a

theorem graded_volume_blowup_projection_component (n : ℕ) (a : RVVolumeIsoSemiring hc C) :
    (rvVolumeGradedBlowupProjection hc C a) n=rvVolumeBlowupProjection hc C n (a n) := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero]; exact (map_zero _).symm
  | of j a =>
    rw [rvVolumeGradedBlowupProjection_of]
    by_cases h : n=j
    · subst j
      rw [DirectSum.of_eq_same,DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ h,DirectSum.of_eq_of_ne _ _ _ h,map_zero]
  | add a b ha hb =>
    rw [map_add]
    change (rvVolumeGradedBlowupProjection hc C a) n+(rvVolumeGradedBlowupProjection hc C b) n=
      rvVolumeBlowupProjection hc C n (a n+b n)
    rw [map_add,ha,hb]

theorem degree_zero_volume_blowup_projection_injective :
    Function.Injective (rvVolumeBlowupProjection hc C 0) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h U =>
    induction b using Quotient.inductionOn with
    | h V =>
      intro h
      exact Quotient.sound (s := rvVolumeIsoSetoid hc C 0) (Quotient.exact h)

theorem raw_volume_kernel_degree_zero (x : RawRVVolumeRing hc C)
    (hx : x ∈ rawVolumeKernelIdeal hc C) : rawVolumeDegreeComponent hc C 0 x=0 := by
  obtain ⟨a,b,hab,hx⟩ := (raw_volume_kernel_mem_iff_positive_pair hc C x).mp hx
  have h0 := congrArg (fun z : RVVolumeBlowupSemiring hc C => z 0) hab
  rw [graded_volume_blowup_projection_component,graded_volume_blowup_projection_component] at h0
  have h0 := degree_zero_volume_blowup_projection_injective hc C h0
  rw [hx,map_sub,raw_volume_degree_component_of,raw_volume_degree_component_of,h0,sub_self]

def rawVolumeHomogeneousAdditiveMap (n : ℕ) :
    Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) →+ RawRVVolumeRing hc C :=
  Algebra.GrothendieckAddGroup.lift
    ((semiringGroupificationOf (RVVolumeIsoSemiring hc C)).toAddMonoidHom.comp
      (DirectSum.of (RVVolumeIsoClasses hc C) n))

theorem raw_volume_homogeneous_component_retraction (n : ℕ)
    (x : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) :
    rawVolumeDegreeComponent hc C n (rawVolumeHomogeneousAdditiveMap hc C n x)=x := by
  have h : (rawVolumeDegreeComponent hc C n).comp (rawVolumeHomogeneousAdditiveMap hc C n)=
      AddMonoidHom.id _ := by
    apply Algebra.GrothendieckAddGroup.addHom_ext
    intro a
    change rawVolumeDegreeComponent hc C n (Algebra.GrothendieckAddGroup.lift _
      (Algebra.GrothendieckAddGroup.of a))=_
    rw [Algebra.GrothendieckAddGroup.lift_apply_of]
    change rawVolumeDegreeComponent hc C n (semiringGroupificationOf _ (DirectSum.of _ n a))=_
    rw [raw_volume_degree_component_of,DirectSum.of_eq_same]
    rfl
  exact DFunLike.congr_fun h x

theorem raw_volume_homogeneous_degree_zero_kernel
    (x : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C 0))
    (hx : rawVolumeHomogeneousAdditiveMap hc C 0 x ∈ rawVolumeKernelIdeal hc C) : x=0 :=
  (raw_volume_homogeneous_component_retraction hc C 0 x).symm.trans
    (raw_volume_kernel_degree_zero hc C _ hx)
end IntegrationInACVF.Section7
