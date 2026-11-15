import Integration7.SupportedOrdinaryVolumeCoefficients
import Integration7.SupportedVolumeJacobianPositiveCoefficients
import Integration7.GradedAEVolumeActionCoherence
import Integration7.GradedSemiringActionLifts

/-! Supported positive homogeneous functions assemble into a genuine
module over the full graded coefficient semiring. The action laws are
transported through the injective maps to the existing AE functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def supportedPositiveComponentAction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (i j : ℕ) :
    RVVolumeBlowupClasses hc C i →+
      (SupportedAERVVolumeFunction hc C X j →+ SupportedAERVVolumeFunction hc C X (i+j)) := by
  cases i with
  | zero =>
    exact (AddMonoidHom.compHom
      (gradedDegreeAddEquiv (F := SupportedAERVVolumeFunction hc C X) (Nat.zero_add j).symm).toAddMonoidHom).comp
      (smulAddHom (RVVolumeBlowupClasses hc C 0) (SupportedAERVVolumeFunction hc C X j))
  | succ p => exact supportedPositiveVolumeCoefficientBiadditive hc C X

theorem supported_volume_forget_degree_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    {i j : ℕ} (h : i=j) (f : SupportedAERVVolumeFunction hc C X i) :
    HEq (supportedVolumeFunctionForget hc C X (gradedDegreeAddEquiv h f))
      (supportedVolumeFunctionForget hc C X f) := by
  cases h
  rfl

theorem supported_positive_component_action_forget
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (i j : ℕ)
    (u : RVVolumeBlowupClasses hc C i) (f : SupportedAERVVolumeFunction hc C X j) :
    supportedVolumeFunctionForget hc C X (supportedPositiveComponentAction hc C X i j u f) =
      gradedShiftComponentAction (aeVolumeFunctionGradedAction hc C n) 1 i j u
        (supportedVolumeFunctionForget hc C X f) := by
  have hR := graded_shift_component_action_heq (aeVolumeFunctionGradedAction hc C n) 1 i j u
    (supportedVolumeFunctionForget hc C X f)
  cases i with
  | zero =>
    have hL := supported_volume_forget_degree_heq hc C X (Nat.zero_add j).symm (u • f)
    rw [supported_volume_forget_smul] at hL
    exact eq_of_heq (hL.trans (hR.trans
      (ae_volume_component_zero_coefficient_heq hc C n (j+1) u
        (supportedVolumeFunctionForget hc C X f))).symm)
  | succ p =>
    exact eq_of_heq ((heq_of_eq (supported_volume_forget_positive_coefficient hc C X u f)).trans hR.symm)

def supportedPositiveGradedAction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    GradedSemiringAction (RVVolumeBlowupClasses hc C) (SupportedAERVVolumeFunction hc C X) :=
  ((aeVolumeFunctionGradedAction hc C n).shift 1).lift
    (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C X)
    (fun _ => supported_volume_function_forget_injective hc C X)
    (supportedPositiveComponentAction hc C X) (supported_positive_component_action_forget hc C X)

abbrev SupportedPositiveGradedVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  DirectSum ℕ (SupportedAERVVolumeFunction hc C X)

instance supportedPositiveGradedVolumeFunctionModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Module (RVVolumeBlowupSemiring hc C) (SupportedPositiveGradedVolumeFunction hc C X) :=
  gradedSemiringActionModule (supportedPositiveGradedAction hc C X)
end IntegrationInACVF.Section7
