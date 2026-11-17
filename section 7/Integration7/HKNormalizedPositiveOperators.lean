module

public import Integration7.HKNormalizedPositiveDegreeFunctions
public import Integration7.NormalizedPositiveDegreeFunctions
public import Integration7.PointNormalizedGradedOperators

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual operators on positive-degree functions descend to the
corrected normalized module from their positive-coefficient laws. The
weighted-zero law follows after normalization, without raw cancellation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

instance legacyActionOnCorrectedPositiveFunctions (n : ℕ) :
    Module (Section7.RVVolumeBlowupSemiring hc C) (PositiveDegreeGradedVolumeFunction hc C n) :=
  Section7.positiveDegreeGradedVolumeFunctionModule hc C n

instance correctedActionOnLegacyPositiveFunctions (n : ℕ) :
    Module (RVVolumeBlowupSemiring hc C) (Section7.PositiveDegreeGradedVolumeFunction hc C n) :=
  positiveDegreeGradedVolumeFunctionModule hc C n

theorem positive_degree_coefficient_action_agrees (n p : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : PositiveDegreeGradedVolumeFunction hc C n) :
    DirectSum.of (RVBlowupClasses hc C) (p+1) u • f =
      DirectSum.of (Section7.RVVolumeBlowupClasses hc C) (p+1) u •
        (f : Section7.PositiveDegreeGradedVolumeFunction hc C n) := by
  induction f using DirectSum.induction_on with
  | zero => rw [smul_zero,smul_zero]
  | add f g hf hg => rw [smul_add,smul_add,hf,hg]
  | of j f =>
    have hNew := graded_semiring_action_of_of ((aeVolumeFunctionGradedAction hc C n).shift 1) (p+1) j u f
    have hOld := graded_semiring_action_of_of ((Section7.aeVolumeFunctionGradedAction hc C n).shift 1) (p+1) j u
      (f : Section7.AEVolumeFunctionComponent hc C n (j+1))
    refine hNew.trans (Eq.trans ?_ hOld.symm)
    apply congrArg (DirectSum.of (fun k => AERVVolumeFunction hc C n k) ((p+1)+j))
    have hH := graded_shift_component_action_heq (aeVolumeFunctionGradedAction hc C n) 1 (p+1) j u f
    have hL := graded_shift_component_action_heq (Section7.aeVolumeFunctionGradedAction hc C n) 1 (p+1) j u f
    exact eq_of_heq (hH.trans hL.symm)

def normalizedPositiveDegreeOperator (n m : ℕ)
    (L : Section7.PositiveDegreeGradedVolumeFunction hc C n →ₗ[Section7.RVVolumeBlowupSemiring hc C]
      Section7.PositiveDegreeGradedVolumeFunction hc C m) :
    NormalizedPositiveDegreeVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedPositiveDegreeVolumeFunction hc C m :=
  pointNormalizedGradedOperator (normalizedVolumeCoefficientMap hc C)
    (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))
    (normalized_volume_coefficient_point hc C) L.toAddMonoidHom (by
      intro i hi u f
      cases i with
      | zero => omega
      | succ p =>
        change L (DirectSum.of (RVBlowupClasses hc C) (p+1) u • f) =
          DirectSum.of (RVBlowupClasses hc C) (p+1) u • L f
        rw [positive_degree_coefficient_action_agrees,positive_degree_coefficient_action_agrees]
        exact L.map_smul _ f)

theorem normalized_positive_degree_operator_generator (n m : ℕ)
    (L : Section7.PositiveDegreeGradedVolumeFunction hc C n →ₗ[Section7.RVVolumeBlowupSemiring hc C]
      Section7.PositiveDegreeGradedVolumeFunction hc C m)
    (f : PositiveDegreeGradedVolumeFunction hc C n) :
    normalizedPositiveDegreeOperator hc C n m L (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ f) =
      scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ (L f) :=
  point_normalized_graded_operator_generator _ _ _ _ _ f

def normalizedVolumeOperatorFromPositive (n m : ℕ)
    (L : Section7.PositiveDegreeGradedVolumeFunction hc C n →ₗ[Section7.RVVolumeBlowupSemiring hc C]
      Section7.PositiveDegreeGradedVolumeFunction hc C m) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C m :=
  (normalizedPositiveDegreeVolumeEquiv hc C m).toLinearMap.comp
    ((normalizedPositiveDegreeOperator hc C n m L).comp
      (normalizedPositiveDegreeVolumeEquiv hc C n).symm.toLinearMap)

theorem normalized_volume_operator_from_positive_generator (n m : ℕ)
    (L : Section7.PositiveDegreeGradedVolumeFunction hc C n →ₗ[Section7.RVVolumeBlowupSemiring hc C]
      Section7.PositiveDegreeGradedVolumeFunction hc C m)
    (f : PositiveDegreeGradedVolumeFunction hc C n) :
    normalizedVolumeOperatorFromPositive hc C n m L
      (normalizedVolumeFunctionGenerator hc C n (gradedShiftToSum (F := AEVolumeFunctionComponent hc C n) 1 f)) =
      normalizedVolumeFunctionGenerator hc C m (gradedShiftToSum (F := AEVolumeFunctionComponent hc C m) 1 (L f)) := by
  rw [← normalized_positive_degree_equiv_generator]
  change normalizedPositiveDegreeVolumeEquiv hc C m
    (normalizedPositiveDegreeOperator hc C n m L
      ((normalizedPositiveDegreeVolumeEquiv hc C n).symm
        (normalizedPositiveDegreeVolumeEquiv hc C n (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ f)))) = _
  rw [(normalizedPositiveDegreeVolumeEquiv hc C n).symm_apply_apply,
    normalized_positive_degree_operator_generator]
  exact normalized_positive_degree_equiv_generator hc C m (L f)

end IntegrationInACVF.Section7.HK
