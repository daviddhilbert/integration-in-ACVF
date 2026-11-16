module

public import Integration7.NormalizedPositiveJacobianIntegrals
public import Integration7.NormalizedVolumeCoordinateInvariance
public import Integration7.VolumeFunctionIntegralPermutationCovariance

@[expose] public section

/-! The actual normalized integral on a homogeneous function is its
canonical geometric integral with homogeneous degree normalized. All
coordinate-only normalizations disappear by the proved point argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem normalized_volume_coefficient_reindex_degree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {a b : ℕ}
    (h : a=b) (x : PositiveVolumeBlowupClasses hc C b) :
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (a+1)
      (positiveVolumeClassReindexDegree hc C h x)) =
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (b+1) x) := by
  cases h
  exact congrArg (fun z => normalizedVolumeCoefficientMap hc C
    (DirectSum.of (RVVolumeBlowupClasses hc C) (a+1) z))
    (eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl x))

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_positive_integral_value {n k : ℕ} (f : AERVVolumeFunction hc C n k) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k f) =
    normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVVolumeBlowupClasses hc C) (((k+1)+n)+1)
        (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)) := by
  let a := aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f
  let σ := appendedToOriginalVolumePermutation (n+1) k
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedVolumeFunctionGenerator hc C n (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f)) = _
  rw [normalized_volume_integral_generator]
  change normalizedVolumeCoefficientMap hc C
    (gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f)) = _
  rw [graded_ae_volume_integral_of]
  change normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (n+(k+1)+1)
    (positiveVolumeClassReindexDegree hc C _ a)) = _
  rw [normalized_volume_coefficient_reindex_degree]
  calc
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (appendVolumeDegree (n+1) k+1) a) =
        normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (appendVolumeDegree (n+1) k+1)
          (positiveVolumeClassPermute hc C σ a)) := normalized_volume_coordinate_invariance hc C σ a
    _ = _ := by
      rw [ae_rv_volume_integral_coordinate_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
      exact normalized_volume_coefficient_reindex_degree hc C (selected_append_degree_eq n k) _

theorem normalized_positive_integral_permute_base {n k : ℕ}
    (f : AERVVolumeFunction hc C n k) (σ : Equiv.Perm (Fin (n+1))) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k (aeRVVolumeFunctionPermuteBase hc C σ f)) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k f) := by
  rw [normalized_positive_integral_value,normalized_positive_integral_value,
    ae_rv_volume_function_integral_permute_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
  exact (normalized_volume_coordinate_invariance hc C _ _).symm

theorem normalized_positive_integral_appended_value {n k : ℕ} (f : AERVVolumeFunction hc C n k) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k f) =
    normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVVolumeBlowupClasses hc C) (appendVolumeDegree (n+1) k+1)
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)) := by
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedVolumeFunctionGenerator hc C n (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f)) = _
  rw [normalized_volume_integral_generator]
  change normalizedVolumeCoefficientMap hc C
    (gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f)) = _
  rw [graded_ae_volume_integral_of]
  exact normalized_volume_coefficient_reindex_degree hc C _ _

end IntegrationInACVF.Section7
