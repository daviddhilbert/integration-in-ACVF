module

public import Integration7.NormalizedVolumeCoefficientRing
public import Integration7.HomogeneousNormalizedRepresentatives

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual normalized coefficient subring consists exactly of
degree-zero fractions with a common homogeneous numerator degree.
The two positive semiring numerators represent their Grothendieck
difference; no commutativity or cancellation is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem normalized_volume_ring_range_iff_homogeneous_fraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (x : VolumePointLocalization hc C) :
    x ∈ (normalizedVolumeRingMap hc C).range ↔
      ∃ n, ∃ a b : RVVolumeBlowupClasses hc C n,
        x = (volumePointLocalizationCoefficients hc C (DirectSum.of (RVVolumeBlowupClasses hc C) n a) -
          volumePointLocalizationCoefficients hc C (DirectSum.of (RVVolumeBlowupClasses hc C) n b)) *
          (↑(volumeLocalizedPointUnit hc C)⁻¹ : VolumePointLocalization hc C)^n := by
  let φ := normalizedVolumeSemiringMap hc C
  let j : RVVolumeBlowupClasses hc C 1 :=
    rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))
  have hj : φ (DirectSum.of (RVVolumeBlowupClasses hc C) 1 j) = 1 :=
    normalized_volume_semiring_point hc C
  rw [normalized_volume_ring_range_iff_difference]
  constructor
  · rintro ⟨a,b,rfl⟩
    obtain ⟨n,a',ha⟩ := normalized_finite_sum_homogeneous φ j hj a
    obtain ⟨m,b',hb⟩ := normalized_finite_sum_homogeneous φ j hj b
    obtain ⟨a'',ha'⟩ := normalized_homogeneous_shift_right φ j hj a' m
    obtain ⟨b'',hb'⟩ := normalized_homogeneous_shift_left φ j hj b' n
    refine ⟨n+m,a'',b'',?_⟩
    change φ a - φ b = _
    rw [ha,hb,ha',hb']
    rw [normalized_volume_semiring_homogeneous,normalized_volume_semiring_homogeneous,sub_mul]
  · rintro ⟨n,a,b,rfl⟩
    refine ⟨DirectSum.of (RVVolumeBlowupClasses hc C) n a,
      DirectSum.of (RVVolumeBlowupClasses hc C) n b,?_⟩
    rw [normalized_volume_semiring_homogeneous,normalized_volume_semiring_homogeneous,sub_mul]

theorem normalized_volume_coefficient_homogeneous
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (x : NormalizedRVVolumeRing hc C) :
    ∃ n, ∃ a b : RVVolumeBlowupClasses hc C n,
      x.val = (volumePointLocalizationCoefficients hc C (DirectSum.of (RVVolumeBlowupClasses hc C) n a) -
        volumePointLocalizationCoefficients hc C (DirectSum.of (RVVolumeBlowupClasses hc C) n b)) *
        (↑(volumeLocalizedPointUnit hc C)⁻¹ : VolumePointLocalization hc C)^n :=
  (normalized_volume_ring_range_iff_homogeneous_fraction hc C x.val).mp x.property

end IntegrationInACVF.Section7
