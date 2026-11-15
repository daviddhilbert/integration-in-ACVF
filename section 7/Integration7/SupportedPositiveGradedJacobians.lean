import Integration7.SupportedPositiveGradedActions
import Integration7.GradedSemiringActionLinearMaps

/-! The actual homogeneous Jacobian transforms assemble into one
linear map over the full graded coefficient semiring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem supported_volume_jacobian_degree_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) {i j : ℕ} (h : i=j)
    (f : SupportedAERVVolumeFunction hc C X i) :
    HEq (supportedVolumeFunctionJacobian hc C φ hφ (gradedDegreeAddEquiv h f))
      (supportedVolumeFunctionJacobian hc C φ hφ f) := by
  cases h
  rfl

theorem supported_positive_graded_jacobian_action
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (i j : ℕ)
    (u : RVVolumeBlowupClasses hc C i) (f : SupportedAERVVolumeFunction hc C X j) :
    supportedVolumeFunctionJacobian hc C φ hφ (supportedPositiveComponentAction hc C X i j u f) =
      supportedPositiveComponentAction hc C Y i j u (supportedVolumeFunctionJacobian hc C φ hφ f) := by
  cases i with
  | zero =>
    have hL := supported_volume_jacobian_degree_heq hc C φ hφ (Nat.zero_add j).symm (u • f)
    have hR := graded_degree_add_equiv_heq (F := SupportedAERVVolumeFunction hc C Y)
      (Nat.zero_add j).symm (u • supportedVolumeFunctionJacobian hc C φ hφ f)
    exact eq_of_heq (hL.trans ((heq_of_eq (supported_volume_jacobian_map_smul hc C φ hφ u f)).trans hR.symm))
  | succ p => exact supported_volume_jacobian_positive_coefficient hc C φ hφ u f

def supportedPositiveGradedJacobian
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedPositiveGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C]
      SupportedPositiveGradedVolumeFunction hc C Y :=
  gradedSemiringActionLinearMap (supportedPositiveGradedAction hc C X)
    (supportedPositiveGradedAction hc C Y)
    (fun j => supportedVolumeJacobianAddHom (k := j) hc C φ hφ)
    (supported_positive_graded_jacobian_action hc C φ hφ)

theorem supported_positive_graded_jacobian_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (j : ℕ)
    (f : SupportedAERVVolumeFunction hc C X j) :
    supportedPositiveGradedJacobian hc C φ hφ (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f) =
      DirectSum.of (SupportedAERVVolumeFunction hc C Y) j (supportedVolumeFunctionJacobian hc C φ hφ f) :=
  graded_component_map_to_sum_of _ j f
end IntegrationInACVF.Section7
