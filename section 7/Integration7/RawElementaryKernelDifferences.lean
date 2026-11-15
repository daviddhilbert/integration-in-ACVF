import Integration7.RawVolumeKernelIdeal
import Integration7.PositiveElementaryBasicGeneration

/-! The actual point-minus-cone relation lies in the raw kernel.
Every elementary source of degree at least two is a left multiple of
this relation in the raw ring. The degree-one converse is not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def rawVolumeObjectClass {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    RawRVVolumeRing hc C := semiringGroupificationOf _ (volumeIsoSemiringClass hc C U)

def rawBasicVolumeDifference : RawRVVolumeRing hc C :=
  rawVolumeObjectClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)) -
    rawVolumeObjectClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))

theorem raw_basic_volume_difference_mem_kernel :
    rawBasicVolumeDifference hc C ∈ rawVolumeKernelIdeal hc C := by
  apply RingHom.mem_ker.mpr
  change rawVolumeBlowupRingProjection hc C
    (semiringGroupificationOf _ (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) -
      semiringGroupificationOf _ (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M)))) = 0
  rw [map_sub]
  change semiringGroupificationMap (rvVolumeGradedBlowupProjection hc C) _ -
    semiringGroupificationMap (rvVolumeGradedBlowupProjection hc C) _ = 0
  rw [semiringGroupificationMap_of,semiringGroupificationMap_of,basic_volume_relation_projection]
  exact sub_self _

theorem raw_basic_span_le_kernel :
    Ideal.span {rawBasicVolumeDifference hc C} ≤ rawVolumeKernelIdeal hc C := by
  apply Ideal.span_le.mpr
  intro x hx
  exact (Set.mem_singleton_iff.mp hx) ▸ raw_basic_volume_difference_mem_kernel hc C

theorem raw_elementary_positive_difference_factor {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)}
    (b : ElementaryBlowup U W) :
    ∃ H : PositiveRVVolumeObject (M := M) (C.base : Set M) k,
      rawVolumeObjectClass hc C (n := k+2) U - rawVolumeObjectClass hc C (n := k+2) W =
        rawVolumeObjectClass hc C (n := k+1) H * rawBasicVolumeDifference hc C := by
  obtain ⟨H,hU,hW⟩ := elementary_positive_semiring_factorization hc C b
  refine ⟨H,?_⟩
  change semiringGroupificationOf _ (volumeIsoSemiringClass hc C (n := k+2) U) -
    semiringGroupificationOf _ (volumeIsoSemiringClass hc C (n := k+2) W) = _
  rw [hU,hW,map_mul,map_mul]
  exact (mul_sub _ _ _).symm

theorem raw_elementary_positive_difference_mem_basic_span {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)}
    (b : ElementaryBlowup U W) :
    rawVolumeObjectClass hc C (n := k+2) U - rawVolumeObjectClass hc C (n := k+2) W ∈
      Ideal.span {rawBasicVolumeDifference hc C} := by
  obtain ⟨H,hH⟩ := raw_elementary_positive_difference_factor hc C b
  rw [hH]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
end IntegrationInACVF.Section7
