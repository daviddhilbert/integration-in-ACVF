import Integration7.NormalizedSupportedUnivEquivalence
import Integration7.NormalizedSupportedVolumeIntegrals
import Integration7.NormalizedPositiveFunctionGeneration

/-! Global definable VF bijections act linearly on the existing full
normalized function module, including ordinary degree zero. The operator
agrees with the actual homogeneous Jacobian transform and preserves total
integration. The domain here is the full VF affine space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedGlobalVolumeJacobian
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  (normalizedSupportedUnivEquiv hc C n).toLinearMap.comp
    ((normalizedSupportedVolumeJacobian hc C φ hφ).comp (normalizedSupportedUnivEquiv hc C n).symm.toLinearMap)

theorem normalized_global_volume_jacobian_positive
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    normalizedGlobalVolumeJacobian hc C φ hφ (normalizedPositiveVolumeFunction hc C n j f) =
      normalizedPositiveVolumeFunction hc C n j (supportedVolumeFunctionForget hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
        (supportedVolumeFunctionJacobian hc C φ hφ (supportedVolumeUnivLift hc C n j f))) := by
  change normalizedSupportedUnivEquiv hc C n
    (normalizedSupportedVolumeJacobian hc C φ hφ
      ((normalizedSupportedUnivEquiv hc C n).symm (normalizedPositiveVolumeFunction hc C n j f))) = _
  rw [normalized_supported_univ_inverse_positive,normalized_supported_volume_jacobian_generator,
    normalized_supported_univ_equiv_forget,normalized_supported_volume_forget_generator]

theorem normalized_global_volume_jacobian_ordinary
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) (f : AEOrdinaryRVVolumeFunction hc C n) :
    normalizedGlobalVolumeJacobian hc C φ hφ
      (normalizedVolumeFunctionGenerator hc C n (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 f)) =
    normalizedPositiveVolumeFunction hc C n 0 (supportedVolumeFunctionForget hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      (supportedVolumeFunctionJacobian hc C φ hφ (supportedVolumeUnivLift hc C n 0
        (aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n 0
          (positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M))) f)))) := by
  rw [normalized_ordinary_function_positive_generator,normalized_global_volume_jacobian_positive]

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_global_volume_change_of_variables
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) (f : NormalizedVolumeFunction hc C n) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (normalizedGlobalVolumeJacobian hc C φ hφ f) := by
  let E := normalizedSupportedUnivEquiv hc C n
  let I := normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  let J := normalizedSupportedVolumeJacobian hc C φ hφ
  have h := normalized_supported_volume_change_of_variables_value hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ (E.symm f)
  change I (normalizedSupportedVolumeForget hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E.symm f)) =
    I (normalizedSupportedVolumeForget hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (J (E.symm f))) at h
  have hSource : normalizedSupportedVolumeForget hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E.symm f)=f :=
    (normalized_supported_univ_equiv_forget hc C n (E.symm f)).symm.trans (E.apply_symm_apply f)
  exact (congrArg I hSource).symm.trans (h.trans
    (congrArg I (normalized_supported_univ_equiv_forget hc C n (J (E.symm f))).symm))
end IntegrationInACVF.Section7
