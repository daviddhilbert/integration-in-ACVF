import Integration7.HKNormalizedVolumeProductCommutativity

/-! Commutativity of the actual normalized coefficient ring, proved
from geometric homogeneous product swaps and point stabilization.
No commutativity of the raw graded semiring is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem normalized_basic_volume_images_commute (a b : RVVolumeIsoSemiring hc C) :
    Commute (normalizedBasicVolumeMap hc C a) (normalizedBasicVolumeMap hc C b) := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add a c ha hc' => simpa only [map_add] using ha.add_left hc'
  | of n a =>
    induction a using Quotient.inductionOn with
    | h U =>
      induction b using DirectSum.induction_on with
      | zero => rw [map_zero]; exact Commute.zero_right _
      | add b c hb hc' => simpa only [map_add] using hb.add_right hc'
      | of m b =>
        induction b using Quotient.inductionOn with
        | h V => exact normalized_basic_homogeneous_classes_commute hc C (n := n) (m := m) U V

theorem normalized_volume_ring_basic_difference (x : NormalizedRVVolumeRing hc C) :
    ∃ a b : RVVolumeIsoSemiring hc C,
      x = normalizedBasicVolumeMap hc C a - normalizedBasicVolumeMap hc C b := by
  obtain ⟨r,rfl⟩ := normalized_volume_ring_projection_surjective hc C x
  obtain ⟨a,b,rfl⟩ := semiringGroupification_exists_difference r
  obtain ⟨a',ha⟩ := rvVolumeGradedBlowupProjection_surjective hc C a
  obtain ⟨b',hb⟩ := rvVolumeGradedBlowupProjection_surjective hc C b
  refine ⟨a',b',?_⟩
  rw [map_sub]
  change normalizedVolumeCoefficientMap hc C a - normalizedVolumeCoefficientMap hc C b =
    normalizedVolumeCoefficientMap hc C (rvVolumeGradedBlowupProjection hc C a') -
      normalizedVolumeCoefficientMap hc C (rvVolumeGradedBlowupProjection hc C b')
  rw [ha,hb]

theorem normalized_volume_ring_mul_comm (x y : NormalizedRVVolumeRing hc C) : x*y = y*x := by
  obtain ⟨a,b,rfl⟩ := normalized_volume_ring_basic_difference hc C x
  obtain ⟨c,d,rfl⟩ := normalized_volume_ring_basic_difference hc C y
  exact (((normalized_basic_volume_images_commute hc C a c).sub_left
      (normalized_basic_volume_images_commute hc C b c)).sub_right
    ((normalized_basic_volume_images_commute hc C a d).sub_left
      (normalized_basic_volume_images_commute hc C b d))).eq

instance normalizedRVVolumeCommRing : CommRing ↥(NormalizedRVVolumeRing hc C) where
  toRing := Subring.toRing (NormalizedRVVolumeRing hc C)
  mul_comm := normalized_volume_ring_mul_comm hc C

end IntegrationInACVF.Section7.HK
