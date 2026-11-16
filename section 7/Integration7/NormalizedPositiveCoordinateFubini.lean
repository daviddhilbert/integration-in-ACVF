module

public import Integration7.NormalizedHomogeneousIntegralValues
public import Integration7.PositiveCoordinateVolumeFubini

@[expose] public section

/-! Fubini for every actual coordinate projection of a positive
homogeneous function in the normalized ring. The coordinate normalizer
is eliminated by proved degree and permutation invariance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}

theorem normalized_canonical_from_appended_value
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ)
    (x : PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k)) :
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (((k+1)+n)+1)
      (canonicalFromAppendedVolumeClass hc C n k x)) =
    normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVVolumeBlowupClasses hc C) (appendVolumeDegree (n+1) k+1) x) := by
  unfold canonicalFromAppendedVolumeClass
  rw [normalized_volume_coefficient_reindex_degree]
  exact (normalized_volume_coordinate_invariance hc C _ x).symm

theorem normalized_coordinate_volume_normalizer_value
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (E : VFCoordinateProjection (n+1) (p+1))
    (x : PositiveVolumeBlowupClasses hc C (appendVolumeDegree (p+1) (appendVolumeDegree E.discarded k))) :
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (((k+1)+n)+1)
      (coordinateVolumeIntegralNormalizer hc C E k x)) =
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C)
      (appendVolumeDegree (p+1) (appendVolumeDegree E.discarded k)+1) x) := by
  unfold coordinateVolumeIntegralNormalizer
  rw [normalized_volume_coefficient_reindex_degree]
  rw [←normalized_volume_coordinate_invariance]
  rw [normalized_canonical_from_appended_value]
  exact normalized_volume_coefficient_reindex_degree hc C (append_volume_degree_split p E.discarded k) x

theorem normalized_positive_coordinate_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (E : VFCoordinateProjection (n+1) (p+1)) (f : AERVVolumeFunction hc C n k) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (normalizedPositiveVolumeFunction hc C p (appendVolumeDegree E.discarded k)
        (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k f) := by
  let g := aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f
  rw [normalized_positive_integral_appended_value,normalized_positive_integral_value]
  calc
    _ = normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (((k+1)+n)+1)
        (coordinateVolumeIntegralNormalizer hc C E k
          (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 g))) :=
      (normalized_coordinate_volume_normalizer_value hc C E _).symm
    _ = _ := congrArg (fun z => normalizedVolumeCoefficientMap hc C
        (DirectSum.of (RVVolumeBlowupClasses hc C) (((k+1)+n)+1) z))
      (normalized_coordinate_volume_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)

end IntegrationInACVF.Section7
