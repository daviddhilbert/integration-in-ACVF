module

public import Integration7.SupportedPositiveGradedActions
public import Integration7.GradedSemiringActionLinearMaps
public import Integration7.GradedShiftLinearEmbeddings

@[expose] public section

/-! The supported positive graded module maps linearly into the full
graded AE module, retaining each actual positive homogeneous component. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def supportedPositiveGradedForget
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedPositiveGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C]
      GradedAEVolumeFunction hc C n :=
  (gradedShiftLinearEmbedding (aeVolumeFunctionGradedAction hc C n) 1).comp
    (gradedSemiringActionLinearMap (supportedPositiveGradedAction hc C X)
      ((aeVolumeFunctionGradedAction hc C n).shift 1)
      (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C X)
      (supported_positive_component_action_forget hc C X))

theorem supported_positive_graded_forget_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : SupportedAERVVolumeFunction hc C X j) :
    supportedPositiveGradedForget hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1) (supportedVolumeFunctionForget hc C X f) := by
  change gradedShiftToSum (F := AEVolumeFunctionComponent hc C n) 1
    (gradedComponentMapToSum (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C X)
      (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f)) = _
  rw [graded_component_map_to_sum_of]
  exact graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 j
    (supportedVolumeFunctionForget hc C X f)
end IntegrationInACVF.Section7
