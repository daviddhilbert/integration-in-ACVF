module

public import Integration7.HKNormalizedVolumeCoefficientRing

@[expose] public section

/-! The actual normalized coefficient ring has the universal property
of setting the geometric degree-one point equal to one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {T : Type*} [Ring T] (g : RVVolumeBlowupRing hc C →+* T)
variable (hj : g (volumePointRing hc C) = 1)

def normalizedVolumeRingLift : NormalizedRVVolumeRing hc C →+* T :=
  (centralAwayLift (volumePointRing hc C) g (hj.symm ▸ isUnit_one)).comp
    (NormalizedRVVolumeRing hc C).subtype

theorem normalized_volume_local_lift_semiring (a : RVVolumeBlowupSemiring hc C) :
    centralAwayLift (volumePointRing hc C) g (hj.symm ▸ isUnit_one)
      (normalizedVolumeSemiringMap hc C a) = g (semiringGroupificationOf _ a) := by
  let L := centralAwayLift (volumePointRing hc C) g (hj.symm ▸ isUnit_one)
  have hunit : L (volumeLocalizedPointUnit hc C : VolumePointLocalization hc C) = 1 := by
    rw [volume_localized_point_unit_value]
    exact (centralAwayLift_map _ g _ _).trans hj
  have hinv : L (↑(volumeLocalizedPointUnit hc C)⁻¹ : VolumePointLocalization hc C) = 1 := by
    have h := congrArg L (volumeLocalizedPointUnit hc C).mul_inv
    rw [map_mul,hunit,one_mul,map_one] at h
    exact h
  change L (normalizedVolumeSemiringMap hc C a) = _
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero,map_zero,map_zero,map_zero]
  | add a b ha hb => rw [map_add,map_add,map_add,map_add,ha,hb]
  | of n a =>
    rw [normalized_volume_semiring_homogeneous,map_mul,map_pow,hinv,one_pow,mul_one]
    exact centralAwayLift_map _ g _ _

theorem normalized_volume_ring_lift_coefficient (a : RVVolumeBlowupSemiring hc C) :
    normalizedVolumeRingLift hc C g hj (normalizedVolumeCoefficientMap hc C a) =
      g (semiringGroupificationOf _ a) := by
  change centralAwayLift (volumePointRing hc C) g (hj.symm ▸ isUnit_one)
    (normalizedVolumeRingMap hc C (semiringGroupificationOf _ a)) = _
  rw [normalizedVolumeRingMap,semiringGroupificationLift_of]
  exact normalized_volume_local_lift_semiring hc C g hj a

theorem normalized_volume_ring_hom_ext
    {f h : NormalizedRVVolumeRing hc C →+* T}
    (heq : ∀ a : RVVolumeBlowupSemiring hc C,
      f (normalizedVolumeCoefficientMap hc C a) = h (normalizedVolumeCoefficientMap hc C a)) : f = h := by
  apply RingHom.ext
  intro x
  obtain ⟨r,rfl⟩ := normalized_volume_ring_projection_surjective hc C x
  obtain ⟨a,b,rfl⟩ := semiringGroupification_exists_difference r
  rw [map_sub,map_sub,map_sub]
  exact congrArg₂ (·-·) (heq a) (heq b)

theorem normalized_volume_ring_lift_unique
    (f : NormalizedRVVolumeRing hc C →+* T)
    (hf : ∀ a : RVVolumeBlowupSemiring hc C,
      f (normalizedVolumeCoefficientMap hc C a) = g (semiringGroupificationOf _ a)) :
    f = normalizedVolumeRingLift hc C g hj := by
  apply normalized_volume_ring_hom_ext hc C
  intro a
  exact (hf a).trans (normalized_volume_ring_lift_coefficient hc C g hj a).symm

end IntegrationInACVF.Section7.HK
