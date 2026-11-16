module

public import Integration7.HKNormalizedFunctionGenerators
public import Integration7.HKPositiveIntegralTransfers
public import Integration7.PositiveGradedCoordinatePushforwards
public import Integration7.PositiveGradedVolumeFubini

@[expose] public section

/-! Actual signed coordinate integrals descend to the whole corrected
normalized function module, and satisfy total Fubini. The descent uses
only proved positive-coefficient laws and point normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedVolumeCoordinateIntegral (E : VFCoordinateProjection (n+1) (p+1)) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C p :=
  normalizedVolumeOperatorFromPositive hc C n p
    (Section7.positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E)

theorem normalized_volume_coordinate_integral_positive (E : VFCoordinateProjection (n+1) (p+1))
    (f : AERVVolumeFunction hc C n k) :
    normalizedVolumeCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (normalizedPositiveVolumeFunction hc C n k f) =
      normalizedPositiveVolumeFunction hc C p (appendVolumeDegree E.discarded k)
        (aeRVVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  let L := Section7.positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
  let g := aeRVVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f
  have h := normalized_volume_operator_from_positive_generator hc C n p L
    (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) k f)
  have hSource := graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 k f
  have hImage : L (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) k f) =
      DirectSum.of (fun j => AEVolumeFunctionComponent hc C p (j+1)) (appendVolumeDegree E.discarded k) g :=
    Section7.positive_graded_signed_coordinate_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E k f
  have hTarget := graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C p) 1
    (appendVolumeDegree E.discarded k) g
  exact (congrArg (fun v => normalizedVolumeOperatorFromPositive hc C n p L
    (normalizedVolumeFunctionGenerator hc C n v)) hSource).symm.trans
      (h.trans ((congrArg (fun v => normalizedVolumeFunctionGenerator hc C p
        (gradedShiftToSum (F := AEVolumeFunctionComponent hc C p) 1 v)) hImage).trans
          (congrArg (normalizedVolumeFunctionGenerator hc C p) hTarget)))

theorem normalized_positive_integral_appended_value (f : AERVVolumeFunction hc C n k) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k f) =
      normalizedVolumeCoefficientMap hc C (DirectSum.of (RVBlowupClasses hc C) (appendVolumeDegree (n+1) k+1)
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)) := by
  have h := normalized_volume_integral_generator hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f)
  have hShift := graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 k f
  have hIntegral := positive_degree_graded_integral_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f
  exact h.trans (congrArg (normalizedVolumeCoefficientMap hc C)
    ((congrArg (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n) hShift).symm.trans hIntegral))

theorem normalized_positive_coordinate_total_fubini (E : VFCoordinateProjection (n+1) (p+1))
    (f : AERVVolumeFunction hc C n k) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (normalizedVolumeCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
        (normalizedPositiveVolumeFunction hc C n k f)) =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (normalizedPositiveVolumeFunction hc C n k f) := by
  rw [normalized_volume_coordinate_integral_positive,normalized_positive_integral_appended_value,
    normalized_positive_integral_appended_value]
  apply congrArg (normalizedVolumeCoefficientMap hc C)
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext
    (by
      change appendVolumeDegree (p+1) (appendVolumeDegree E.discarded k)+1=appendVolumeDegree (n+1) k+1
      have h := volume_projection_index_eq E
      simp only [append_volume_degree_eq] at *
      omega)
    (positive_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f))

theorem normalized_coordinate_total_fubini (E : VFCoordinateProjection (n+1) (p+1)) :
    (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p).comp
      (normalizedVolumeCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E) =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n := by
  apply normalized_volume_function_linearMap_ext_positive hc C n
  intro k f
  exact normalized_positive_coordinate_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f

end IntegrationInACVF.Section7.HK
