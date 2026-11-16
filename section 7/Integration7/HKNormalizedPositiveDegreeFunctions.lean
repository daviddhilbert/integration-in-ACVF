import Integration7.GradedPointNormalization
import Integration7.HKNormalizedVolumeFunctions

/-! Positive graded functions give the same actual normalized module
as the full finite graded space. The inverse pads by the genuine central
point coefficient, including on ordinary degree-zero components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev PositiveDegreeGradedVolumeFunction (n : ℕ) :=
  DirectSum ℕ (fun j => AEVolumeFunctionComponent hc C n (j+1))

instance positiveDegreeGradedVolumeFunctionModule (n : ℕ) :
    Module (RVVolumeBlowupSemiring hc C) (PositiveDegreeGradedVolumeFunction hc C n) :=
  gradedSemiringActionModule ((aeVolumeFunctionGradedAction hc C n).shift 1)

abbrev NormalizedPositiveDegreeVolumeFunction (n : ℕ) :=
  SemimoduleScalarExtension (normalizedVolumeCoefficientMap hc C) (PositiveDegreeGradedVolumeFunction hc C n)

def normalizedPositiveDegreeVolumeEquiv (n : ℕ) :
    NormalizedPositiveDegreeVolumeFunction hc C n ≃ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  gradedPointNormalizationEquiv (normalizedVolumeCoefficientMap hc C) (aeVolumeFunctionGradedAction hc C n)
    (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))
    (volume_point_class_commutes hc C) (normalized_volume_coefficient_point hc C)

theorem normalized_positive_degree_equiv_generator (n : ℕ)
    (f : PositiveDegreeGradedVolumeFunction hc C n) :
    normalizedPositiveDegreeVolumeEquiv hc C n
        (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ f) =
      normalizedVolumeFunctionGenerator hc C n (gradedShiftToSum (F := AEVolumeFunctionComponent hc C n) 1 f) := by
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C)
    (gradedShiftLinearEmbedding (aeVolumeFunctionGradedAction hc C n) 1)
    (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ f) = _
  exact scalar_extension_map_generator _ _ f

theorem normalized_positive_degree_equiv_inverse_generator (n : ℕ)
    (f : GradedAEVolumeFunction hc C n) :
    (normalizedPositiveDegreeVolumeEquiv hc C n).symm (normalizedVolumeFunctionGenerator hc C n f) =
      scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _
        (gradedPointPaddingAddHom (aeVolumeFunctionGradedAction hc C n)
          (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) f) := by
  change scalarExtensionMap (normalizedVolumeCoefficientMap hc C)
    (gradedPointPaddingLinearMap (aeVolumeFunctionGradedAction hc C n)
      (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))
      (volume_point_class_commutes hc C))
    (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ f) = _
  exact scalar_extension_map_generator _ _ f
end IntegrationInACVF.Section7.HK
