module

public import Integration7.HKSupportedGradedVolumeFunctions
public import Integration7.HKGradedAEVolumeIntegralAddHoms
public import Integration7.RawPositiveGradedChangeOfVariables

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Raw change of variables for every finite graded supported function,
including actual weighted-zero values. No point padding is cancelled. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem supported_volume_component_jacobian_integral
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (j : ℕ)
    (f : SupportedVolumeFunctionComponent hc C X j) :
    aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
      (supportedVolumeComponentForgetAddHom hc C Y j
        (supportedVolumeComponentJacobianAddHom hc C φ hφ j f)) =
    aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
      (supportedVolumeComponentForgetAddHom hc C X j f) := by
  cases j with
  | zero => exact (supported_zero_volume_function_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f).symm
  | succ k =>
    have h : n+(k+1)=appendVolumeDegree (n+1) k := by rw [append_volume_degree_eq]; omega
    exact congrArg (positiveVolumeClassDegreeReindexAddEquiv hc C h)
      (raw_positive_appended_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f)

def rawSupportedGradedIntegralAddHom
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedGradedVolumeFunction hc C X →+ RVVolumeBlowupSemiring hc C :=
  (gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (supportedGradedVolumeForgetAddHom hc C X)

theorem raw_supported_graded_integral_of
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : SupportedVolumeFunctionComponent hc C X j) :
    rawSupportedGradedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
      (DirectSum.of _ j f) =
    DirectSum.of (RVBlowupClasses hc C) ((n+j)+1)
      (aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
        (supportedVolumeComponentForgetAddHom hc C X j f)) := by
  change gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (supportedGradedVolumeForgetAddHom hc C X (DirectSum.of _ j f)) = _
  rw [supported_graded_volume_forget_of,graded_ae_volume_integral_of]

theorem raw_graded_change_of_variables
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    (rawSupportedGradedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (supportedGradedVolumeJacobianAddHom hc C φ hφ) =
      rawSupportedGradedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply AddMonoidHom.ext
  intro f
  change rawSupportedGradedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
    (supportedGradedVolumeJacobianAddHom hc C φ hφ f) = _
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    rw [supported_graded_volume_jacobian_of,raw_supported_graded_integral_of,
      raw_supported_graded_integral_of,supported_volume_component_jacobian_integral]

end IntegrationInACVF.Section7.HK
