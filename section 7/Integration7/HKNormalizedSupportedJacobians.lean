module

public import Integration7.HKNormalizedRestrictedJacobians
public import Integration7.HKNormalizedSupportedCoordinateIntegrals
public import Integration7.RawPositiveGradedChangeOfVariables

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The genuine normalized Jacobian operator maps source support into
target support and preserves the integral, including weighted-zero
supported functions through the proved positive generation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem normalized_restricted_jacobian_preserves_support
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : NormalizedVolumeFunction hc C n)
    (hf : f ∈ normalizedVolumeSupport hc C X) :
    normalizedRestrictedVolumeJacobian hc C φ hφ f ∈ normalizedVolumeSupport hc C Y := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k,f,rfl⟩ := hg
    rw [normalized_restricted_volume_jacobian_positive]
    exact normalized_positive_generator_has_support hc C Y k _ ⟨_,rfl⟩
  | zero => simpa only [map_zero] using (normalizedVolumeSupport hc C Y).zero_mem
  | add f g hf hg ihf ihg =>
    rw [map_add]
    exact (normalizedVolumeSupport hc C Y).add_mem ihf ihg
  | smul r f hf ih =>
    rw [map_smul]
    exact (normalizedVolumeSupport hc C Y).smul_mem r ih

def normalizedSupportedVolumeJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedSupportedVolumeFunction hc C Y :=
  LinearMap.codRestrict _ ((normalizedRestrictedVolumeJacobian hc C φ hφ).comp
    (normalizedVolumeSupport hc C X).subtype)
    (fun f => normalized_restricted_jacobian_preserves_support hc C φ hφ f.val f.property)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_restricted_jacobian_integral
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : NormalizedVolumeFunction hc C n)
    (hf : f ∈ normalizedVolumeSupport hc C X) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedRestrictedVolumeJacobian hc C φ hφ f) =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k,f,rfl⟩ := hg
    rw [normalized_restricted_volume_jacobian_positive,normalized_positive_integral_appended_value,
      normalized_positive_integral_appended_value]
    exact congrArg (fun v => normalizedVolumeCoefficientMap hc C
      (DirectSum.of (RVBlowupClasses hc C) (appendVolumeDegree (n+1) k+1) v))
        (raw_positive_appended_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f)
  | zero => simp only [map_zero]
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul r f hf ih => simp only [map_smul,ih]

theorem normalized_supported_volume_change_of_variables
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : NormalizedSupportedVolumeFunction hc C X) :
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f =
      normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
        (normalizedSupportedVolumeJacobian hc C φ hφ f) :=
  (normalized_restricted_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f.val f.property).symm

end IntegrationInACVF.Section7.HK
