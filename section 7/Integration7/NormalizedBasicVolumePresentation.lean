import Integration7.NormalizedVolumeUniversalProperty
import Integration7.LocalizedVolumeBlowupDescent

/-! The actual normalized ring is universal for the concrete geometric
relations point = cone = 1. Degree-one relations are handled by proved
point stabilization, without the unlocalized principal-kernel claim. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedBasicVolumeMap : RVVolumeIsoSemiring hc C →+* NormalizedRVVolumeRing hc C :=
  (normalizedVolumeCoefficientMap hc C).comp (rvVolumeGradedBlowupProjection hc C)

theorem normalized_basic_volume_point :
    normalizedBasicVolumeMap hc C
      (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) = 1 := by
  change normalizedVolumeCoefficientMap hc C
    (rvVolumeGradedBlowupProjection hc C (volumeIsoSemiringClass hc C (n := 1)
      (degreeOnePointVolumeObject (C.base : Set M)))) = 1
  rw [volumeIsoSemiringClass,rvVolumeGradedBlowupProjection_of]
  exact normalized_volume_coefficient_point hc C

theorem normalized_basic_volume_cone :
    normalizedBasicVolumeMap hc C
      (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))) = 1 := by
  change normalizedVolumeCoefficientMap hc C
    (rvVolumeGradedBlowupProjection hc C (volumeIsoSemiringClass hc C (n := 1)
      (degreeOneConeVolumeObject (C.base : Set M)))) = 1
  rw [←basic_volume_relation_projection]
  exact normalized_basic_volume_point hc C

variable {T : Type*} [Ring T] (f : RVVolumeIsoSemiring hc C →+* T)
variable (hj : f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) = 1)
variable (hcone : f (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))) = 1)

def normalizedBasicVolumeRingMap : RVVolumeBlowupRing hc C →+* T :=
  semiringGroupificationLift (localizedVolumeBlowupDescend hc C f (hj.symm ▸ isUnit_one) (hj.trans hcone.symm))

theorem normalized_basic_volume_ring_point :
    normalizedBasicVolumeRingMap hc C f hj hcone (volumePointRing hc C) = 1 := by
  rw [volumePointRing,normalizedBasicVolumeRingMap,semiringGroupificationLift_of]
  change localizedVolumeBlowupDescend hc C f (hj.symm ▸ isUnit_one) (hj.trans hcone.symm)
    (DirectSum.of (RVVolumeBlowupClasses hc C) 1
      (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))) = 1
  rw [localized_volume_blowup_descend_class]
  exact hj

def normalizedBasicVolumeLift : NormalizedRVVolumeRing hc C →+* T :=
  normalizedVolumeRingLift hc C (normalizedBasicVolumeRingMap hc C f hj hcone)
    (normalized_basic_volume_ring_point hc C f hj hcone)

theorem normalized_basic_volume_lift_map (a : RVVolumeIsoSemiring hc C) :
    normalizedBasicVolumeLift hc C f hj hcone (normalizedBasicVolumeMap hc C a) = f a := by
  change normalizedVolumeRingLift hc C _ _
    (normalizedVolumeCoefficientMap hc C (rvVolumeGradedBlowupProjection hc C a)) = _
  rw [normalized_volume_ring_lift_coefficient,normalizedBasicVolumeRingMap,semiringGroupificationLift_of]
  exact RingHom.congr_fun
    (localized_volume_blowup_descend_projection hc C f (hj.symm ▸ isUnit_one) (hj.trans hcone.symm)) a

theorem normalized_basic_volume_hom_ext
    {g h : NormalizedRVVolumeRing hc C →+* T}
    (heq : ∀ a, g (normalizedBasicVolumeMap hc C a) = h (normalizedBasicVolumeMap hc C a)) : g = h := by
  apply normalized_volume_ring_hom_ext hc C
  intro a
  obtain ⟨b,rfl⟩ := rvVolumeGradedBlowupProjection_surjective hc C a
  exact heq b

theorem normalized_basic_volume_lift_unique
    (g : NormalizedRVVolumeRing hc C →+* T)
    (hg : ∀ a, g (normalizedBasicVolumeMap hc C a) = f a) :
    g = normalizedBasicVolumeLift hc C f hj hcone := by
  apply normalized_basic_volume_hom_ext hc C
  intro a
  exact (hg a).trans (normalized_basic_volume_lift_map hc C f hj hcone a).symm

end IntegrationInACVF.Section7
