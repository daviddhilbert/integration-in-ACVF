import Integration7.HKNormalizedVolumeSupports
import Integration7.HKNormalizedCoordinateFubini

/-! Normalized coordinate integration lands on the literal projected
support, including all actual weighted-zero supported generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_coordinate_integral_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : NormalizedVolumeFunction hc C n) (hf : f ∈ normalizedVolumeSupport hc C X) :
    normalizedVolumeCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f ∈
      normalizedVolumeSupport hc C (pureVFCoordinateImage X E.retainedIndex) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k,f,rfl⟩ := hg
    rw [normalized_volume_coordinate_integral_positive]
    exact normalized_positive_generator_has_support hc C _ _ _
      (raw_positive_signed_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E _ ⟨f,rfl⟩)
  | zero => simpa only [map_zero] using (normalizedVolumeSupport hc C _).zero_mem
  | add f g hf hg ihf ihg =>
    rw [map_add]
    exact (normalizedVolumeSupport hc C _).add_mem ihf ihg
  | smul r f hf ih =>
    rw [map_smul]
    exact (normalizedVolumeSupport hc C _).smul_mem r ih

def normalizedSupportedCoordinateIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedSupportedVolumeFunction hc C (pureVFCoordinateImage X E.retainedIndex) :=
  LinearMap.codRestrict _
    ((normalizedVolumeCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E).comp
      (normalizedVolumeSupport hc C X).subtype)
    (fun f => normalized_coordinate_integral_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f.val f.property)

def normalizedSupportedVolumeIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C] NormalizedRVVolumeRing hc C :=
  (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp (normalizedVolumeSupport hc C X).subtype

theorem normalized_supported_coordinate_total_fubini
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : NormalizedSupportedVolumeFunction hc C X) :
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X E.retainedIndex)
      (normalizedSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f) =
      normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f :=
  LinearMap.congr_fun (normalized_coordinate_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E) f.val

end IntegrationInACVF.Section7.HK
