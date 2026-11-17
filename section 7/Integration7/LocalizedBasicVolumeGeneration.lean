module

public import Integration7.PositiveElementaryBasicGeneration
public import Integration7.ElementaryVolumeProducts
public import Integration7.IteratedVolumeBlowups
public import Mathlib.Algebra.Group.Units.Basic

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! After the point becomes a unit, the basic point/cone relation
forces every actual elementary and common-blowup relation, including
degree one. Stabilization raises that boundary case to degree two.
This does not assert the unlocalized principal-ideal statement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem volume_iso_semiring_class_iso {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    volumeIsoSemiringClass hc C (n := k+1) U = volumeIsoSemiringClass hc C (n := k+1) V :=
  congrArg (DirectSum.of (RVVolumeIsoClasses hc C) (k+1)) (positiveVolumeIsoClass_iso hc C e)

theorem volume_iso_semiring_class_coprod {k : ℕ}
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    volumeIsoSemiringClass hc C (n := k+1) (U.coprod V) =
      volumeIsoSemiringClass hc C (n := k+1) U + volumeIsoSemiringClass hc C (n := k+1) V := by
  letI : AddCommMonoid (RVVolumeIsoClasses hc C (k+1)) := rvVolumeIsoClassesAddCommMonoid hc C (k+1)
  exact map_add (DirectSum.of (RVVolumeIsoClasses hc C) (k+1))
    (rvVolumeIsoClass hc C (n := k+1) U) (rvVolumeIsoClass hc C (n := k+1) V)

variable {R : Type*} [Semiring R] (f : RVVolumeIsoSemiring hc C →+* R)
variable (hj : IsUnit (f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))))
variable (hBasic : f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) =
  f (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))))
include hj hBasic

theorem localized_elementary_volume_image_eq {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) =
      f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  cases k with
  | zero =>
    apply hj.mul_left_cancel
    have h := elementary_positive_image_eq_of_basic hc C f hBasic
      (b.product_left (degreeOnePointVolumeObject (C.base : Set M)))
    simpa only [volume_iso_semiring_class_positive_product,map_mul] using h
  | succ k => exact elementary_positive_image_eq_of_basic hc C f hBasic b

theorem localized_volume_blowup_image_eq {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : VolumeBlowup U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) =
      f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  rw [volume_iso_semiring_class_iso hc C b.sourceIso,
    volume_iso_semiring_class_iso hc C b.targetIso,
    volume_iso_semiring_class_coprod,volume_iso_semiring_class_coprod,map_add,map_add,
    localized_elementary_volume_image_eq hc C f hj hBasic b.elementary]

theorem localized_iterated_volume_image_eq {k d : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : IteratedVolumeBlowup d U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) =
      f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  induction b with
  | refl U => rfl
  | step b h ih => exact (localized_volume_blowup_image_eq hc C f hj hBasic b.some).trans ih

theorem localized_common_volume_blowup_image_eq {k : ℕ}
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : VolumeBlowupEquivalent U W) :
    f (volumeIsoSemiringClass hc C (n := k+1) U) =
      f (volumeIsoSemiringClass hc C (n := k+1) W) := by
  obtain ⟨a,b,U',W',hU,hW,⟨e⟩⟩ := b
  exact (localized_iterated_volume_image_eq hc C f hj hBasic hU).trans
    ((congrArg f (volume_iso_semiring_class_iso hc C e)).trans
      (localized_iterated_volume_image_eq hc C f hj hBasic hW).symm)

end IntegrationInACVF.Section7
