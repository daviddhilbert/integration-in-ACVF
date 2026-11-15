import Integration7.ElementaryPrincipalVolumeFactors
import Integration7.AllDegreeVolumeIsoSemiring
import Integration7.GradedVolumeBlowupProjection

/-! In every degree at least two, the actual elementary relation is
forced by the single concrete degree-one point/cone relation. This is
stated in the actual graded semiring, without assuming the desired
identification of its full kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeIsoSemiringClass
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) : RVVolumeIsoSemiring hc C :=
  DirectSum.of (RVVolumeIsoClasses hc C) n (rvVolumeIsoClass hc C (n := n) U)

theorem volume_iso_semiring_class_positive_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {i j : ℕ}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) i)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) j) :
    volumeIsoSemiringClass hc C (n := (i+1)+(j+1)) (U.prod V) =
      volumeIsoSemiringClass hc C (n := i+1) U * volumeIsoSemiringClass hc C (n := j+1) V := by
  exact (DirectSum.of_mul_of
    (rvVolumeIsoClass hc C (n := i+1) U) (rvVolumeIsoClass hc C (n := j+1) V)).symm

theorem elementary_positive_semiring_factorization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)}
    (b : ElementaryBlowup U W) :
    ∃ H : PositiveRVVolumeObject (M := M) (C.base : Set M) k,
      volumeIsoSemiringClass hc C (n := k+2) U = volumeIsoSemiringClass hc C (n := k+1) H *
        volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)) ∧
      volumeIsoSemiringClass hc C (n := k+2) W = volumeIsoSemiringClass hc C (n := k+1) H *
        volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M)) := by
  obtain ⟨H,⟨hU⟩,⟨hW⟩⟩ := elementary_volume_positive_factorization hc C b
  refine ⟨H,?_,?_⟩
  · rw [←volume_iso_semiring_class_positive_product]
    exact congrArg (DirectSum.of (RVVolumeIsoClasses hc C) (k+2)) (positiveVolumeIsoClass_iso hc C hU)
  · rw [←volume_iso_semiring_class_positive_product]
    exact congrArg (DirectSum.of (RVVolumeIsoClasses hc C) (k+2)) (positiveVolumeIsoClass_iso hc C hW)

theorem elementary_positive_image_eq_of_basic
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {R : Type*} [Semiring R] (f : RVVolumeIsoSemiring hc C →+* R)
    (hBasic : f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) =
      f (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))))
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)}
    (b : ElementaryBlowup U W) :
    f (volumeIsoSemiringClass hc C (n := k+2) U) = f (volumeIsoSemiringClass hc C (n := k+2) W) := by
  obtain ⟨H,hU,hW⟩ := elementary_positive_semiring_factorization hc C b
  rw [hU,hW,map_mul,map_mul,hBasic]

theorem basic_volume_relation_projection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    rvVolumeGradedBlowupProjection hc C
        (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) =
      rvVolumeGradedBlowupProjection hc C
        (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))) := by
  rw [volumeIsoSemiringClass,volumeIsoSemiringClass,rvVolumeGradedBlowupProjection_of,
    rvVolumeGradedBlowupProjection_of]
  exact congrArg (DirectSum.of (RVVolumeBlowupClasses hc C) 1)
    ((positiveVolumeBlowupClass_eq_iff hc C).mpr (degree_one_basic_volume_relation hc C))

end IntegrationInACVF.Section7
