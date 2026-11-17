module

public import Integration7.StabilizedVolumeCoordinateIsomorphisms
public import Integration7.HKNormalizedBasicVolumePresentation
public import Integration7.NormalizedVolumeCoordinateInvariance
public import Integration7.VolumeClassCoordinatePermutations
public import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every unsigned volume-coordinate permutation becomes invisible in
the actual normalized coefficient ring. The proof first gives a full
volume isomorphism after multiplying by the point, then uses point=1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem normalized_basic_volume_coordinate_invariance
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := k+1) U) =
      normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := k+1) (U.permuteVolume σ)) := by
  have h := congrArg (normalizedBasicVolumeMap hc C)
    (volume_iso_semiring_class_iso hc C (pointStabilizedVolumeCoordinateIso hc C U σ))
  rw [volume_iso_semiring_class_positive_product,volume_iso_semiring_class_positive_product,
    map_mul,map_mul,normalized_basic_volume_point,mul_one,mul_one] at h
  exact h

theorem normalized_basic_volume_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C U) =
      normalizedVolumeCoefficientMap hc C
        (DirectSum.of (RVBlowupClasses hc C) n (rvVolumeBlowupClass hc C U)) := by
  change normalizedVolumeCoefficientMap hc C (rvVolumeGradedBlowupProjection hc C
    (DirectSum.of (RVVolumeIsoClasses hc C) n (rvVolumeIsoClass hc C U))) = _
  rw [rvVolumeGradedBlowupProjection_of]
  rfl

set_option maxHeartbeats 1200000 in
theorem normalized_volume_coordinate_invariance
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (σ : Equiv.Perm (Fin (k+1))) (a : PositiveVolumeBlowupClasses hc C k) :
    normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVBlowupClasses hc C) (k+1) a) =
    normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVBlowupClasses hc C) (k+1) (positiveVolumeClassPermute hc C σ a)) := by
  induction a using Quotient.inductionOn with
  | h U =>
    exact (normalized_basic_volume_class hc C (n := k+1) U).symm.trans
      ((normalized_basic_volume_coordinate_invariance hc C (k := k) U σ).trans
        (normalized_basic_volume_class hc C (n := k+1) (U.permuteVolume σ)))

end IntegrationInACVF.Section7.HK
