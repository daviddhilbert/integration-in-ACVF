module

public import Integration7.HKNormalizedVolumeCoordinateInvariance
public import Integration7.NormalizedVolumeProductCommutativity
public import Integration7.HKZeroCoefficientSymmetry

@[expose] public section

/-! All homogeneous raw RV volume classes commute after normalization.
Positive products are compared by their exact unsigned swap chart;
ordinary degree zero is raised to positive degree by the point=1 relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem volume_iso_semiring_class_reindex_degree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {a b : ℕ}
    (h : a=b) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) b) :
    volumeIsoSemiringClass hc C (n := a+1) (U.reindexDegree h) = volumeIsoSemiringClass hc C (n := b+1) U := by
  cases h
  exact volume_iso_semiring_class_iso hc C (volumeCastReindexIso hc C U rfl)

set_option maxHeartbeats 1200000 in
theorem normalized_basic_positive_classes_commute
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    Commute (normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := n+1) U))
      (normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := m+1) V)) := by
  calc
    _ = normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := (n+1)+(m+1)) (U.prod V)) := by
      rw [volume_iso_semiring_class_positive_product,map_mul]
    _ = normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := (n+1)+(m+1))
        ((U.prod V).permuteVolume (positiveProductSwapPermutation n m))) :=
      normalized_basic_volume_coordinate_invariance hc C (k := (n+1)+m) _ _
    _ = normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := (n+1)+(m+1)) (unsignedProductSwapObject U V)) :=
      congrArg (normalizedBasicVolumeMap hc C) (volume_iso_semiring_class_iso hc C (k := (n+1)+m) (volumeUnsignedSwapPermutedIso hc C U V))
    _ = normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := (m+1)+(n+1)) (V.prod U)) :=
      congrArg (normalizedBasicVolumeMap hc C)
        (volume_iso_semiring_class_reindex_degree hc C (positiveProduct_degree_swap n m) (V.prod U))
    _ = _ := by rw [volume_iso_semiring_class_positive_product,map_mul]

theorem volume_iso_semiring_class_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) (V : RVVolumeObject (M := M) (C.base : Set M) m) :
    volumeIsoSemiringClass hc C (n := n+m) (product (C.base : Set M) n m U V) =
      volumeIsoSemiringClass hc C U * volumeIsoSemiringClass hc C V :=
  (DirectSum.of_mul_of (rvVolumeIsoClass hc C (n := n) U) (rvVolumeIsoClass hc C (n := m) V)).symm

theorem normalized_basic_homogeneous_positive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C U) =
      normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C (n := n+1)
        (product (C.base : Set M) n 1 U (degreeOnePointVolumeObject (C.base : Set M)))) := by
  rw [volume_iso_semiring_class_product,map_mul,normalized_basic_volume_point,mul_one]

theorem normalized_basic_homogeneous_classes_commute
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) (V : RVVolumeObject (M := M) (C.base : Set M) m) :
    Commute (normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C U))
      (normalizedBasicVolumeMap hc C (volumeIsoSemiringClass hc C V)) := by
  rw [normalized_basic_homogeneous_positive hc C U,normalized_basic_homogeneous_positive hc C V]
  exact normalized_basic_positive_classes_commute hc C _ _

end IntegrationInACVF.Section7.HK
