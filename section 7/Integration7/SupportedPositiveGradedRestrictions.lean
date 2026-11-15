import Integration7.AERVVolumeRestrictionCoefficients
import Integration7.SupportedPositiveGradedActions
import Integration7.GradedSemiringActionLinearMaps
import Integration7.NormalizedPositiveDegreeFunctions

/-! The positive graded supported module is an actual retract of the
full positive graded AE module, linearly over every coefficient degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_volume_restriction_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    {i j : ℕ} (h : i=j) {f : AERVVolumeFunction hc C n i} {g : AERVVolumeFunction hc C n j}
    (hf : HEq f g) :
    HEq (aeVolumeFunctionRestrictToSupported hc C X f) (aeVolumeFunctionRestrictToSupported hc C X g) := by
  cases h
  cases hf
  rfl

theorem positive_graded_restriction_component_action
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (i j : ℕ)
    (u : RVVolumeBlowupClasses hc C i) (f : AERVVolumeFunction hc C n j) :
    aeVolumeFunctionRestrictToSupported hc C X
      (gradedShiftComponentAction (aeVolumeFunctionGradedAction hc C n) 1 i j u f) =
    supportedPositiveComponentAction hc C X i j u (aeVolumeFunctionRestrictToSupported hc C X f) := by
  have hSource := graded_shift_component_action_heq (aeVolumeFunctionGradedAction hc C n) 1 i j u f
  cases i with
  | zero =>
    have h := hSource.trans (ae_volume_component_zero_coefficient_heq hc C n (j+1) u f)
    have hL := ae_volume_restriction_heq hc C X (Nat.zero_add j) h
    have hR := graded_degree_add_equiv_heq (F := SupportedAERVVolumeFunction hc C X)
      (Nat.zero_add j).symm (u • aeVolumeFunctionRestrictToSupported hc C X f)
    exact eq_of_heq (hL.trans ((heq_of_eq (ae_volume_restriction_ordinary_coefficient hc C X u f)).trans hR.symm))
  | succ p =>
    exact eq_of_heq ((ae_volume_restriction_heq hc C X rfl hSource).trans
      (heq_of_eq (ae_volume_restriction_positive_coefficient hc C X u f)))

def positiveGradedVolumeRestriction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    PositiveDegreeGradedVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C]
      SupportedPositiveGradedVolumeFunction hc C X :=
  gradedSemiringActionLinearMap ((aeVolumeFunctionGradedAction hc C n).shift 1)
    (supportedPositiveGradedAction hc C X)
    (fun j => aeVolumeRestrictionAddHom (k := j) hc C X)
    (positive_graded_restriction_component_action hc C X)

def supportedPositiveGradedForgetShift
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedPositiveGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C]
      PositiveDegreeGradedVolumeFunction hc C n :=
  gradedSemiringActionLinearMap (supportedPositiveGradedAction hc C X)
    ((aeVolumeFunctionGradedAction hc C n).shift 1)
    (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C X)
    (supported_positive_component_action_forget hc C X)

theorem positive_graded_volume_restriction_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveGradedVolumeRestriction hc C X (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) j f) =
      DirectSum.of (SupportedAERVVolumeFunction hc C X) j (aeVolumeFunctionRestrictToSupported hc C X f) :=
  graded_component_map_to_sum_of _ j f

theorem positive_graded_volume_restriction_forget
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    (positiveGradedVolumeRestriction hc C X).comp (supportedPositiveGradedForgetShift hc C X) = LinearMap.id := by
  apply LinearMap.ext
  intro g
  change positiveGradedVolumeRestriction hc C X (supportedPositiveGradedForgetShift hc C X g) = g
  induction g using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    change gradedComponentMapToSum (fun j => aeVolumeRestrictionAddHom (k := j) hc C X)
      (gradedComponentMapToSum (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C X)
        (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f)) = _
    rw [graded_component_map_to_sum_of,graded_component_map_to_sum_of]
    exact congrArg (DirectSum.of (SupportedAERVVolumeFunction hc C X) j)
      (ae_volume_restriction_forget_supported hc C X f)
end IntegrationInACVF.Section7
