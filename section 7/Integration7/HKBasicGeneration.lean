import Integration7.HKPositiveBasicGeneration
import Integration7.HKDegreeOnePrincipalFactors

/-! A single point/cone relation forces every elementary relation, including
degree one. The degree-one proof uses its genuine weighted zero factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem volume_iso_semiring_class_iso {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    volumeIsoSemiringClass hc C (n := k+1) U = volumeIsoSemiringClass hc C (n := k+1) V :=
  congrArg (DirectSum.of (RVVolumeIsoClasses hc C) (k+1)) (Quotient.sound ⟨e⟩)

theorem volume_iso_semiring_class_coprod {k : ℕ}
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    volumeIsoSemiringClass hc C (n := k+1) (U.coprod V) =
      volumeIsoSemiringClass hc C (n := k+1) U + volumeIsoSemiringClass hc C (n := k+1) V := by
  letI : AddCommMonoid (RVVolumeIsoClasses hc C (k+1)) := rvVolumeIsoClassesAddCommMonoid hc C (k+1)
  exact map_add (DirectSum.of (RVVolumeIsoClasses hc C) (k+1))
    (rvVolumeIsoClass hc C (n := k+1) U) (rvVolumeIsoClass hc C (n := k+1) V)

theorem elementary_degree_one_semiring_factorization
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) 0} (b : ElementaryBlowup U W) :
    ∃ H : ZeroRVVolumeObject (M := M) (C.base : Set M),
      volumeIsoSemiringClass hc C (n := 1) U = volumeIsoSemiringClass hc C (n := 0) H *
        volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)) ∧
      volumeIsoSemiringClass hc C (n := 1) W = volumeIsoSemiringClass hc C (n := 0) H *
        volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M)) := by
  obtain ⟨H,⟨hU⟩,⟨hW⟩⟩ := elementary_degree_one_product_factorization hc C b
  refine ⟨H,?_,?_⟩
  · rw [volumeIsoSemiringClass,volumeIsoSemiringClass,volumeIsoSemiringClass,DirectSum.of_mul_of]
    exact congrArg (DirectSum.of (RVVolumeIsoClasses hc C) 1) (Quotient.sound ⟨hU⟩)
  · rw [volumeIsoSemiringClass,volumeIsoSemiringClass,volumeIsoSemiringClass,DirectSum.of_mul_of]
    exact congrArg (DirectSum.of (RVVolumeIsoClasses hc C) 1) (Quotient.sound ⟨hW⟩)

variable {R : Type*} [Semiring R] (f : RVVolumeIsoSemiring hc C →+* R)
variable (hBasic : f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) =
  f (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))))
include hBasic

theorem elementary_image_eq_of_basic {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) = f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  cases k with
  | zero =>
    obtain ⟨H,hU,hW⟩ := elementary_degree_one_semiring_factorization hc C b
    rw [hU,hW,map_mul,map_mul,hBasic]
  | succ k => exact elementary_positive_image_eq_of_basic hc C f hBasic b

theorem blowup_image_eq_of_basic {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : VolumeBlowup U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) = f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  rw [volume_iso_semiring_class_iso hc C b.sourceIso,volume_iso_semiring_class_iso hc C b.targetIso,
    volume_iso_semiring_class_coprod,volume_iso_semiring_class_coprod,map_add,map_add,
    elementary_image_eq_of_basic hc C f hBasic b.elementary]

theorem iterated_image_eq_of_basic {k d : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : IteratedVolumeBlowup d U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) = f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  induction b with
  | refl U => rfl
  | step b h ih => exact (blowup_image_eq_of_basic hc C f hBasic b.some).trans ih

theorem common_blowup_image_eq_of_basic {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (h : VolumeBlowupEquivalent U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) = f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  obtain ⟨a,b,U',W',hU,hW,⟨e⟩⟩ := h
  exact (iterated_image_eq_of_basic hc C f hBasic hU).trans
    ((congrArg f (volume_iso_semiring_class_iso hc C e)).trans
      (iterated_image_eq_of_basic hc C f hBasic hW).symm)

end IntegrationInACVF.Section7.HK
