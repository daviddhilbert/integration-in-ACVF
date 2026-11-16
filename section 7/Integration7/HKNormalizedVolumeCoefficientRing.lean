import Integration7.HKCentralVolumePointRing
import Integration7.CentralAwayLocalization
import Integration7.GradedSemiringUnitNormalization

/-! Actual normalized RV coefficients: localize the proved geometric
quotient ring at its central point and normalize each homogeneous term.
The resulting subring consists exactly of differences of normalized
finite homogeneous sums. No principal-kernel identification is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev VolumePointLocalization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) := CentralAway (volumePointRing hc C)

def volumePointLocalizationMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeBlowupRing hc C →+* VolumePointLocalization hc C := centralAwayMap (volumePointRing hc C)

def volumePointLocalizationCoefficients
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeBlowupSemiring hc C →+* VolumePointLocalization hc C :=
  (volumePointLocalizationMap hc C).comp (semiringGroupificationOf (RVVolumeBlowupSemiring hc C))

def volumeLocalizedPointUnit
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) : (VolumePointLocalization hc C)ˣ :=
  (centralAwayMap_point_isUnit (volumePointRing hc C)).unit

theorem volume_localized_point_unit_value
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (volumeLocalizedPointUnit hc C : VolumePointLocalization hc C) =
      volumePointLocalizationMap hc C (volumePointRing hc C) :=
  (centralAwayMap_point_isUnit (volumePointRing hc C)).unit_spec

theorem volume_localized_coefficients_commute_point
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a : RVVolumeBlowupSemiring hc C) :
    Commute (volumePointLocalizationCoefficients hc C a) (volumeLocalizedPointUnit hc C : VolumePointLocalization hc C) := by
  rw [volume_localized_point_unit_value]
  exact (volume_point_ring_commutes hc C (semiringGroupificationOf _ a)).map
    (volumePointLocalizationMap hc C).toMonoidHom

def normalizedVolumeSemiringMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeBlowupSemiring hc C →+* VolumePointLocalization hc C :=
  gradedSemiringUnitNormalize (volumePointLocalizationCoefficients hc C) (volumeLocalizedPointUnit hc C)
    (volume_localized_coefficients_commute_point hc C)

theorem normalized_volume_semiring_homogeneous
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (n : ℕ) (a : RVBlowupClasses hc C n) :
    normalizedVolumeSemiringMap hc C (DirectSum.of (RVBlowupClasses hc C) n a) =
      volumePointLocalizationCoefficients hc C (DirectSum.of (RVBlowupClasses hc C) n a) *
        (↑(volumeLocalizedPointUnit hc C)⁻¹ : VolumePointLocalization hc C)^n :=
  graded_semiring_unit_normalize_of _ _ _ n a

theorem normalized_volume_semiring_point
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    normalizedVolumeSemiringMap hc C (volumePointClass hc C) = 1 := by
  apply graded_semiring_unit_normalize_point _ _ _ _
  exact (volume_localized_point_unit_value hc C).symm

def normalizedVolumeRingMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeBlowupRing hc C →+* VolumePointLocalization hc C :=
  semiringGroupificationLift (normalizedVolumeSemiringMap hc C)

abbrev NormalizedRVVolumeRing
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) := (normalizedVolumeRingMap hc C).range

def normalizedVolumeRingProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeBlowupRing hc C →+* NormalizedRVVolumeRing hc C := (normalizedVolumeRingMap hc C).rangeRestrict

theorem normalized_volume_ring_projection_surjective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Function.Surjective (normalizedVolumeRingProjection hc C) := RingHom.rangeRestrict_surjective _

def normalizedVolumeCoefficientMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeBlowupSemiring hc C →+* NormalizedRVVolumeRing hc C :=
  (normalizedVolumeRingProjection hc C).comp (semiringGroupificationOf (RVVolumeBlowupSemiring hc C))

theorem normalized_volume_coefficient_point
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    normalizedVolumeCoefficientMap hc C (volumePointClass hc C) = 1 := by
  apply Subtype.ext
  change normalizedVolumeRingMap hc C (semiringGroupificationOf _ (volumePointClass hc C)) = 1
  rw [normalizedVolumeRingMap,semiringGroupificationLift_of]
  exact normalized_volume_semiring_point hc C

theorem normalized_volume_ring_range_iff_difference
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (x : VolumePointLocalization hc C) :
    x ∈ (normalizedVolumeRingMap hc C).range ↔
      ∃ a b : RVVolumeBlowupSemiring hc C,
        x = normalizedVolumeSemiringMap hc C a - normalizedVolumeSemiringMap hc C b := by
  constructor
  · rintro ⟨r,rfl⟩
    obtain ⟨a,b,rfl⟩ := semiringGroupification_exists_difference r
    exact ⟨a,b,by rw [map_sub,normalizedVolumeRingMap,semiringGroupificationLift_of,semiringGroupificationLift_of]⟩
  · rintro ⟨a,b,rfl⟩
    exact ⟨semiringGroupificationOf _ a - semiringGroupificationOf _ b,
      by rw [map_sub,normalizedVolumeRingMap,semiringGroupificationLift_of,semiringGroupificationLift_of]⟩

end IntegrationInACVF.Section7.HK
