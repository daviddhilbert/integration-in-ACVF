module

public import Integration7.RawPositiveSupportedFubini
public import Integration7.SupportedPositiveGradedJacobians

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Jacobian transform preserves the raw graded integral on
supported positive function values. Ordinary coefficients remain part of
the full scalar semiring. No assertion on ordinary-valued inputs is made. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem raw_positive_appended_jacobian_integral
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : SupportedAERVVolumeFunction hc C X k) :
    aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (supportedVolumeFunctionForget hc C Y (supportedVolumeFunctionJacobian hc C φ hφ f)) =
    aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (supportedVolumeFunctionForget hc C X f) := by
  apply canonical_from_appended_injective hc C n k
  rw [ae_rv_volume_integral_from_appended,ae_rv_volume_integral_from_appended]
  exact (supported_volume_function_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f).symm

def rawSupportedPositiveGradedIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedPositiveGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C] RVVolumeBlowupSemiring hc C :=
  (positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (supportedPositiveGradedForgetShift hc C X)

theorem raw_supported_positive_graded_integral_of
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : SupportedAERVVolumeFunction hc C X j) :
    rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X (DirectSum.of _ j f) =
      DirectSum.of (RVVolumeBlowupClasses hc C) (appendVolumeDegree (n+1) j+1)
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
          (supportedVolumeFunctionForget hc C X f)) := by
  change positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (gradedComponentMapToSum (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C X) (DirectSum.of _ j f)) = _
  rw [graded_component_map_to_sum_of,positive_graded_ae_volume_integral_of]
  rfl

theorem raw_positive_graded_change_of_variables
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    (rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (supportedPositiveGradedJacobian hc C φ hφ) =
      rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  change rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
    (supportedPositiveGradedJacobian hc C φ hφ f) = _
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    rw [supported_positive_graded_jacobian_of,raw_supported_positive_graded_integral_of,
      raw_supported_positive_graded_integral_of,raw_positive_appended_jacobian_integral]
end IntegrationInACVF.Section7
