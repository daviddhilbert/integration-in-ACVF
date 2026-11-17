module

public import Integration7.HKGlobalJacobianCoefficientLaws
public import Integration7.HKGradedAEVolumeActionCoherence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The genuine all-degree global Jacobian operator is linear over
the full corrected coefficient semiring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
  (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))) (hφ : Function.Bijective φ)

theorem global_jacobian_component_weighted_smul (j : ℕ)
    (z : RVBlowupClasses hc C 0) (f : AEVolumeFunctionComponent hc C n j) :
    aeVolumeComponentJacobianAddHom hc C φ hφ j (z • f) =
      z • aeVolumeComponentJacobianAddHom hc C φ hφ j f := by
  cases j with
  | zero => exact global_jacobian_zero_weighted_smul hc C φ hφ z f
  | succ k => exact global_jacobian_positive_weighted_smul hc C φ hφ z f

theorem global_jacobian_component_degree_heq {i j : ℕ} (h : i=j)
    {f : AEVolumeFunctionComponent hc C n i} {g : AEVolumeFunctionComponent hc C n j} (hfg : HEq f g) :
    HEq (aeVolumeComponentJacobianAddHom hc C φ hφ i f) (aeVolumeComponentJacobianAddHom hc C φ hφ j g) := by
  cases h
  cases hfg
  rfl

theorem global_jacobian_component_coefficient (i j : ℕ)
    (u : RVBlowupClasses hc C i) (f : AEVolumeFunctionComponent hc C n j) :
    aeVolumeComponentJacobianAddHom hc C φ hφ (i+j)
        (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f) =
      aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u
        (aeVolumeComponentJacobianAddHom hc C φ hφ j f) := by
  cases i with
  | zero =>
    have hL := global_jacobian_component_degree_heq hc C φ hφ (Nat.zero_add j)
      (ae_volume_component_zero_coefficient_heq hc C n j u f)
    exact eq_of_heq (hL.trans ((heq_of_eq
      (global_jacobian_component_weighted_smul hc C φ hφ j u f)).trans
        (ae_volume_component_zero_coefficient_heq hc C n j u _).symm))
  | succ p =>
    cases j with
    | zero => exact global_jacobian_zero_positive_coefficient hc C φ hφ u f
    | succ k => exact global_jacobian_positive_positive_coefficient hc C φ hφ u f

def gradedAEVolumeJacobianLinearMap :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C n :=
  gradedSemiringActionLinearMap (aeVolumeFunctionGradedAction hc C n) (aeVolumeFunctionGradedAction hc C n)
    (aeVolumeComponentJacobianAddHom hc C φ hφ) (global_jacobian_component_coefficient hc C φ hφ)

theorem graded_ae_volume_jacobian_linear_value (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeJacobianLinearMap hc C φ hφ f = gradedAEVolumeJacobianAddHom hc C φ hφ f := rfl

end IntegrationInACVF.Section7.HK
