import Integration7.NormalizedSupportedVolumeFunctions

/-! Change of variables holds on every element of the actual balanced
normalized supported module, by linear extension of the proved geometric
homogeneous identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedSupportedVolumeIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C] NormalizedRVVolumeRing hc C :=
  (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (normalizedSupportedVolumeForget hc C X)

theorem normalized_supported_volume_change_of_variables
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X =
      (normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
        (normalizedSupportedVolumeJacobian hc C φ hφ) := by
  apply scalar_extension_linearMap_ext (normalizedVolumeCoefficientMap hc C)
  intro g
  change normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
      (normalizedSupportedVolumeGenerator hc C X g) =
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
      (normalizedSupportedVolumeJacobian hc C φ hφ (normalizedSupportedVolumeGenerator hc C X g))
  induction g using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (normalizedSupportedVolumeForget hc C X
          (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f))) =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (normalizedSupportedVolumeForget hc C Y
          (normalizedSupportedVolumeJacobian hc C φ hφ
            (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f))))
    rw [normalized_supported_volume_jacobian_generator,normalized_supported_volume_forget_generator,
      normalized_supported_volume_forget_generator]
    exact normalized_positive_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f

theorem normalized_supported_volume_change_of_variables_value
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : NormalizedSupportedVolumeFunction hc C X) :
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f =
      normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
        (normalizedSupportedVolumeJacobian hc C φ hφ f) :=
  congrArg (fun I => I f) (normalized_supported_volume_change_of_variables hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ)
end IntegrationInACVF.Section7
